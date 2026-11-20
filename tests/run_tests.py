#!/usr/bin/env python3
"""Differential tests: the Lean `Path.clean` and `Path.join` against a
model of Go's rules and three implementations.

The tool answers `clean` and `join` requests (see the header of
Main.lean). Its answers are checked two ways.

1. Against the model, written from the documentation of Go's
   `path.Clean` and `path.Join` and sharing nothing with the Lean
   code. It has two parts, and they must agree on every path whose
   cleaning is checked below:

   - `rules_clean` splits the path into its elements and applies the
     four rules of the documentation, one at a time, until none
     applies: drop an empty element (rule 1, and the slash at the end),
     drop a `.` (rule 2), drop a `..` and the name before it (rule 3),
     drop a `..` at the start of a rooted path (rule 4). The rule and
     the place it applies at are picked at random, from a recorded
     seed, so the order differs from path to path. It then writes the
     elements back, after a slash if the path is rooted, and gives `.`
     for nothing.
   - `model_clean` reads the elements once, left to right, with a
     stack, as Rob Pike's "Lexical File Names in Plan 9" does. It is
     fast enough for long inputs, which `rules_clean` is not.

   `model_join` is the documentation of `Join`: the empty elements left
   out, the rest joined by slashes and cleaned, and the empty string
   when nothing is left. The model must also give every result in Go's
   own tests of Clean and Join (`cleantests` and `jointests` in
   src/path/path_test.go). Every answer of the tool must equal the
   model's.

2. Against three oracles, on every request each can answer:

   - Go: `path.Clean` and `path.Join` of the Go standard library, the
     installed toolchain, through tests/oracles/go/main.go;
   - Python: `posixpath.normpath`, through
     tests/oracles/python/oracle.py; `posixpath.join` keeps only the
     last rooted argument, so it is not asked `join`;
   - Node: `path.posix.normalize` and `path.posix.join`, through
     tests/oracles/node/oracle.js.

   An oracle that cannot be built or started is left out, and the
   record says so on its `- Oracles left out:` line. A disagreement is
   allowed only for a named reason that the model confirms, with the
   oracle's own rule:

   - Python keeps two slashes at the start of a path, and only two, as
     POSIX allows ("A pathname that begins with two successive slashes
     may be interpreted in an implementation-defined manner"); the
     model confirms it when Python gives `/` and then the model's
     result.
   - Node keeps a slash at the end of a path; the model confirms it
     when the path ends in a slash and Node gives the model's result
     and then a slash.
   - Node's `join` gives `.`, not the empty string, when every element
     is empty or there are none; and keeps a slash at the end as
     `normalize` does.

   Any other disagreement is a failure. Each named one is counted.

Inputs come from a recorded seed, after fixed sets:

- Go's `cleantests` (each path, and each result) and `jointests`, a
  join of an empty element and a rooted one, and the paths of Pike's
  paper;
- every path of up to 10 characters over `a`, `.` and `/`, and of up
  to 7 over `a`, `b`, `.` and `/`;
- random paths of up to 80 characters, built from `/`, `.`, `..`,
  names, and characters that are not ASCII, a space, a tab, a
  backslash, NUL, CR and LF;
- random joins of zero to five elements, among them empty ones;
- long inputs of about a million characters: names, `..`, `.`,
  slashes, and deep paths that `..` takes back to the start; the time
  they take is recorded;
- malformed requests, which the tool must answer with `error`, among
  them hex that is not UTF-8;
- the command-line modes `clean` and `join`, among them arguments that
  are not UTF-8, which the Lean runtime replaces with U+FFFD, and wrong
  arguments: what each run prints on standard output and its exit
  status.

Every seventh request ends in CR LF.

    python3 tests/run_tests.py [--seed N] [--count N] [--no-oracles]

`--count` is the number of random paths; half as many random joins are
made. `--no-oracles` leaves every oracle out and compares the tool with
the model alone, as tests/plant_bugs.py does. The script builds the
executable and the oracles first, writes tests/TEST-RESULTS.md, and
exits non-zero if any check fails.
"""

import argparse
import itertools
import os
import random
import subprocess
import sys
import threading
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "path"
TESTS = ROOT / "tests"
ORACLES = TESTS / "oracles"
GO_SRC = ORACLES / "go"
GO_EXE = ROOT / ".lake" / "oracle-go" / "go-oracle"
PY_ORACLE = ORACLES / "python" / "oracle.py"
NODE_ORACLE = ORACLES / "node" / "oracle.js"
RESULTS = TESTS / "TEST-RESULTS.md"
TIMEOUT = 3600
BUILD_TIMEOUT = 3600
# The requests are split among this many `path serve` processes.
JOBS = max(1, min(4, os.cpu_count() or 1))

# ---------------------------------------------------------------------
# The model.

DOT, DOTDOT = ".", ".."
CRLF = "\r\n"


def is_name(e):
    return e not in ("", DOT, DOTDOT)


def render(rooted, es):
    """The path with the elements `es`: a slash first when it is
    rooted, `.` when it is empty and not rooted."""
    s = "/".join(es)
    if rooted:
        return "/" + s
    return s or "."


def rules_clean(p, rng):
    """Go's four rules, applied one at a time, at a place picked by
    `rng`, until none applies."""
    rooted = p.startswith("/")
    es = p.split("/")
    while True:
        moves = []
        for i, e in enumerate(es):
            if e == "":
                moves.append(("empty", i))          # rule 1
            elif e == DOT:
                moves.append(("dot", i))            # rule 2
            elif e == DOTDOT and i > 0 and is_name(es[i - 1]):
                moves.append(("parent", i))         # rule 3
        if rooted and es and es[0] == DOTDOT:
            moves.append(("root", 0))               # rule 4
        if not moves:
            return render(rooted, es)
        rule, i = rng.choice(moves)
        if rule == "parent":
            del es[i - 1:i + 1]
        else:
            del es[i]


def model_clean(p):
    """The elements read once, with a stack."""
    rooted = p.startswith("/")
    stack = []
    for e in p.split("/"):
        if e in ("", DOT):
            continue
        if e == DOTDOT:
            if stack and stack[-1] != DOTDOT:
                stack.pop()
            elif not rooted:
                stack.append(DOTDOT)
            continue
        stack.append(e)
    return render(rooted, stack)


def model_join(es):
    kept = [e for e in es if e != ""]
    if not kept:
        return ""
    return model_clean("/".join(kept))


# Go's tests: src/path/path_test.go, go1.24.7. Copyright 2009 The Go Authors,
# under the BSD-3-Clause license in LICENSES/Go-LICENSE.
GO_CLEAN = [
    ("", "."), ("abc", "abc"), ("abc/def", "abc/def"), ("a/b/c", "a/b/c"), (".", "."),
    ("..", ".."), ("../..", "../.."), ("../../abc", "../../abc"), ("/abc", "/abc"), ("/", "/"),
    ("abc/", "abc"), ("abc/def/", "abc/def"), ("a/b/c/", "a/b/c"), ("./", "."), ("../", ".."),
    ("../../", "../.."), ("/abc/", "/abc"),
    ("abc//def//ghi", "abc/def/ghi"), ("//abc", "/abc"), ("///abc", "/abc"),
    ("//abc//", "/abc"), ("abc//", "abc"),
    ("abc/./def", "abc/def"), ("/./abc/def", "/abc/def"), ("abc/.", "abc"),
    ("abc/def/ghi/../jkl", "abc/def/jkl"), ("abc/def/../ghi/../jkl", "abc/jkl"),
    ("abc/def/..", "abc"), ("abc/def/../..", "."), ("/abc/def/../..", "/"),
    ("abc/def/../../..", ".."), ("/abc/def/../../..", "/"),
    ("abc/def/../../../ghi/jkl/../../../mno", "../../mno"),
    ("abc/./../def", "def"), ("abc//./../def", "def"), ("abc/../../././../def", "../../def"),
]
GO_JOIN = [
    ([], ""), ([""], ""), (["a"], "a"), (["a", "b"], "a/b"), (["a", ""], "a"), (["", "b"], "b"),
    (["/", "a"], "/a"), (["/", ""], "/"), (["a/", "b"], "a/b"), (["a/", ""], "a"), (["", ""], ""),
]
# Paths from Rob Pike, "Lexical File Names in Plan 9, or Getting Dot-Dot
# Right", and a few more at the edges of the rules.
MORE_PATHS = ["/usr/rob/..", "/usr/rob/../..", "/usr/rob/../../..", "../../../a", "a/../../b",
              "/../a/..", "./.././a", "a/./b/./c/./", "...", "a/.../b", ".a/..b/a.", "a/..b/..",
              "....//....", "/./", "//", "///", "//..", "//../a", "/a//../b", " ", " /..", "\\..",
              "a\\..\\b", "é/../ü", "日本/../語", "\x00/..", "a\nb/../c", "a\r/..", "\t/./"]

# ---------------------------------------------------------------------
# Requests.


def hx(s):
    return s.encode("utf-8").hex() or "-"


def request(op, args):
    return " ".join([op] + [hx(a) for a in args])


def model(op, args):
    if op == "clean":
        return "OK " + hx(model_clean(args[0]))
    return "OK " + hx(model_join(args))


def model_line(raw):
    """What the tool must answer to a request line, malformed or not."""
    line = raw[:-1] if raw.endswith("\n") else raw
    if line.endswith("\r") and raw.endswith("\n"):
        line = line[:-1]
    fs = line.split(" ")

    def field(f):
        if f == "-":
            return ""
        if not f or len(f) % 2 or any(c not in "0123456789abcdef" for c in f):
            return None
        try:
            return bytes.fromhex(f).decode("utf-8")
        except ValueError:
            return None

    if fs[0] == "clean" and len(fs) == 2:
        p = field(fs[1])
        return "error" if p is None else model("clean", [p])
    if fs[0] == "join":
        es = [field(f) for f in fs[1:]]
        return "error" if any(e is None for e in es) else model("join", es)
    return "error"


MALFORMED = [
    "", "clean", "clean 61 62", "clean 6", "clean 4A", "clean 0x61", "clean zz", "clean ",
    "clean  61", "Clean 61", "CLEAN 61", "clean\t61", "clean 61 ", " clean 61", "clean --",
    # not UTF-8: a lone continuation octet, an overlong slash, a surrogate,
    # past U+10FFFF, a cut sequence
    "clean ff", "clean 80", "clean c0af", "clean eda080", "clean f4908080", "clean e282",
    "join 6", "join ff", "join 61 ", "join  61", "join 61 zz", "join -- 61", "joins 61",
    "normalize 61", "clean2 61", "x",
]
# Last lines with no LF, with CR LF, with a lone CR: (request, answer).
AT_EOF = [("clean 2f2e2e", "OK 2f"), ("clean 612f2e2e\r\n", "OK 2e"),
          ("join 61 62", "OK 612f62"), ("clean 61\r", "error")]

# ---------------------------------------------------------------------
# Inputs: (label, op, args).

ATOMS = ["/", "/", "/", ".", ".", "..", "a", "b", "abc", "x.y", "...", "é", "日本", "😀", " ",
         "\t", "\\", "\x00", "\n", "\r", "//", "./", "../"]


def random_path(rng, n):
    return "".join(rng.choice(ATOMS) for _ in range(rng.randrange(n + 1)))[:n]


def exhaustive():
    for n in range(11):
        for t in itertools.product("a./", repeat=n):
            yield ("every path over a . / up to 10", "clean", ["".join(t)])
    for n in range(8):
        for t in itertools.product("ab./", repeat=n):
            if "b" in t:
                yield ("every path over a b . / up to 7", "clean", ["".join(t)])


def long_inputs():
    m = 1_000_000
    return [
        ("long", "clean", ["a/" * (m // 2)]),
        ("long", "clean", ["x" * m]),
        ("long", "clean", ["/" * m]),
        ("long", "clean", ["./" * (m // 2)]),
        ("long", "clean", ["../" * (m // 3)]),
        ("long", "clean", ["/" + "../" * (m // 3)]),
        ("long", "clean", ["/" + "a/" * (m // 4) + "../" * (m // 6)]),
        ("long", "clean", ["a/" * (m // 4) + "../" * (m // 4)]),
        ("long", "clean", ["a/" * (m // 4) + "../" * (m // 3)]),
        ("long", "clean", ["a/b/../" * (m // 7)]),
        ("long", "clean", ["abcdefghij/" * (m // 22) + "../" * (m // 66)]),
        ("long", "join", ["a/" * (m // 4), "../" * (m // 6), "b" * 1000]),
    ]


def inputs(seed, count):
    rng = random.Random(seed)
    for p, r in GO_CLEAN:
        yield ("Go cleantests", "clean", [p])
        yield ("Go cleantests, the result", "clean", [r])
    for es, _ in GO_JOIN:
        yield ("Go jointests", "join", es)
    yield ("an empty first element, a rooted second", "join", ["", "/etc"])
    for p in MORE_PATHS:
        yield ("Pike, and edges", "clean", [p])
    yield from exhaustive()
    for _ in range(count):
        yield ("random path", "clean", [random_path(rng, rng.choice([8, 20, 80]))])
    for _ in range(count // 2):
        k = rng.randrange(6)
        es = [random_path(rng, rng.choice([0, 3, 8, 20])) for _ in range(k)]
        yield ("random join", "join", es)
    yield from long_inputs()


# ---------------------------------------------------------------------
# Running a program over request lines.

def run_lines(cmd, lines, timeout=TIMEOUT, cwd=None, env=None):
    """Send `lines` to `cmd` and return its answer lines and a note on
    how the run failed, or None."""
    raw = "".join(lines).encode("utf-8")
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, cwd=cwd, env=env)
    out, err = bytearray(), bytearray()

    def feed():
        try:
            proc.stdin.write(raw)
            proc.stdin.close()
        except (BrokenPipeError, ValueError):
            pass

    def drain(stream, buf):
        while chunk := stream.read1(1 << 16):
            buf += chunk

    threads = [threading.Thread(target=feed),
               threading.Thread(target=drain, args=(proc.stdout, out)),
               threading.Thread(target=drain, args=(proc.stderr, err))]
    for t in threads:
        t.start()
    problem = None
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        problem = f"no end after {timeout} seconds"
    for t in threads:
        t.join()
    proc.wait()
    if proc.returncode != 0 and not problem:
        tail = " / ".join(err.decode("utf-8", "backslashreplace").splitlines()[-3:])
        problem = f"exit status {proc.returncode}: {tail}"
    text = bytes(out).decode("utf-8", "backslashreplace")
    if text and not text.endswith("\n"):
        problem = problem or "the last answer has no LF"
    answers = text.split("\n")
    if answers and answers[-1] == "":
        answers.pop()
    return answers, problem


def run_parallel(cmd, lines, jobs):
    """`run_lines` over `jobs` processes, each given a run of the lines
    in order; the answers in order, and the problems."""
    size = -(-len(lines) // jobs) if lines else 0
    chunks = [lines[k:k + size] for k in range(0, len(lines), size)] if size else [[]]
    results = [None] * len(chunks)

    def one(k):
        results[k] = run_lines(cmd, chunks[k])

    threads = [threading.Thread(target=one, args=(k,)) for k in range(len(chunks))]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    answers, problems = [], []
    for chunk, (got, problem) in zip(chunks, results):
        if problem:
            problems.append(problem)
        if len(got) != len(chunk):
            problems.append(f"{len(got)} answers for {len(chunk)} requests")
            got = (got + [""] * len(chunk))[:len(chunk)]
        answers += got
    return answers, problems


# ---------------------------------------------------------------------
# The oracles. Each setup returns an object with `name`, `version` and
# `answers(lines)`, or raises OracleUnavailable.

class OracleUnavailable(Exception):
    pass


class ProcessOracle:
    def __init__(self, name, version, cmd):
        self.name, self.version, self.cmd = name, version, cmd

    def answers(self, lines):
        got, problem = run_lines(self.cmd, lines)
        if problem or len(got) != len(lines):
            raise RuntimeError(f"{self.name} oracle: "
                               f"{problem or f'{len(got)} answers for {len(lines)} requests'}")
        return got


def first_line(cmd, cwd=None):
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=300, cwd=cwd)
        return (out.stdout or out.stderr).strip().splitlines()[0]
    except (OSError, subprocess.SubprocessError, IndexError):
        return "unknown"


def setup_go():
    GO_EXE.parent.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, GOFLAGS="-mod=readonly", CGO_ENABLED="0", GOTOOLCHAIN="local")
    try:
        subprocess.run(["go", "build", "-o", str(GO_EXE), "."], cwd=GO_SRC, check=True, env=env,
                       capture_output=True, timeout=BUILD_TIMEOUT)
    except (OSError, subprocess.SubprocessError) as e:
        raise OracleUnavailable(f"`go build` did not build it: {e}")
    return ProcessOracle("Go", f"`path.Clean` and `path.Join` of the standard library of "
                         f"{first_line(['go', 'version'])}", [str(GO_EXE)])


def setup_python():
    version = first_line([sys.executable, "-I", "--version"])
    return ProcessOracle("Python", f"`posixpath.normpath` of {version}",
                         [sys.executable, "-I", str(PY_ORACLE)])


def setup_node():
    version = first_line(["node", "--version"])
    if version == "unknown":
        raise OracleUnavailable("`node` is not installed")
    return ProcessOracle("Node", f"`path.posix.normalize` and `path.posix.join` of Node "
                         f"{version}", ["node", str(NODE_ORACLE)])


ORACLE_SETUPS = [("Go", setup_go), ("Python", setup_python), ("Node", setup_node)]

TWO_SLASHES = "Python keeps two slashes at the start of a path, as POSIX allows"
TRAILING = "Node keeps a slash at the end of a path"
JOIN_EMPTY = "Node's `join` gives `.` when every element is empty, or there are none"


def difference_reason(oracle, op, args, want, theirs):
    """The named reason, confirmed by the model, for an oracle that
    answers `theirs` where the model answers `want`; or None."""
    if oracle == "Python" and op == "clean":
        p = args[0]
        if p.startswith("//") and not p.startswith("///") and \
                theirs == "OK " + hx("/" + model_clean(p)):
            return TWO_SLASHES
    if oracle == "Node":
        if op == "clean":
            p = args[0]
            if p.endswith("/") and theirs == "OK " + hx(model_clean(p) + "/"):
                return TRAILING
        if op == "join":
            kept = [e for e in args if e != ""]
            if not kept and theirs == "OK " + hx("."):
                return JOIN_EMPTY
            joined = "/".join(kept)
            if kept and joined.endswith("/") and \
                    theirs == "OK " + hx(model_clean(joined) + "/"):
                return TRAILING + " (in `join`)"
    return None


# ---------------------------------------------------------------------
# The command line.

def cli_cases():
    """Runs of the command-line modes: (arguments, what the run must
    print on standard output, without the last LF, and its exit
    status), from the model."""
    cases = []
    for p in ["", "a//b/../c/", "/../x", "..", "é/./ü/", "a b/ c"]:
        cases.append((["clean", p], model_clean(p), 0))
    for es in [[], [""], ["a", "b"], ["", "/etc"], ["/", "..", "x/"], ["a", "", "", "b"]]:
        cases.append((["join"] + es, model_join(es), 0))
    # Arguments that are not UTF-8: the Lean runtime replaces each run of
    # such octets with U+FFFD before `main` sees them, as Python's
    # "replace" does for these.
    for raw in [b"\xc3/x/.", b"a\xff/../b\xff"]:
        cases.append((["clean", raw], model_clean(raw.decode("utf-8", "replace")), 0))
    cases.append((["join", b"\xff", "b"], model_join(["\ufffd", "b"]), 0))
    for args in [[], ["bogus"], ["clean"], ["clean", "a", "b"], ["serve", "x"], ["Clean", "a"]]:
        cases.append((args, "", 2))
    return cases


def run_cli(cases):
    right, failures = 0, []
    for args, out, status in cases:
        try:
            p = subprocess.run([str(EXE)] + args, capture_output=True, timeout=60)
            got, code_ = p.stdout.decode("utf-8", "backslashreplace"), p.returncode
            if got.endswith("\n"):
                got = got[:-1]
        except (OSError, subprocess.SubprocessError) as e:
            got, code_ = str(e), None
        if (got, code_) == (out, status):
            right += 1
        else:
            failures.append((f"path {' '.join(repr(a) for a in args)}",
                             f"{out!r}, exit {status}", f"{short(got, 160)!r}, exit {code_}"))
    return right, failures

# ---------------------------------------------------------------------


def lean_version():
    try:
        out = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT,
                             capture_output=True, text=True, errors="backslashreplace",
                             timeout=300)
        first = out.stdout.strip().splitlines()[:1]
        return first[0] if first else "unknown"
    except (OSError, subprocess.TimeoutExpired):
        return "unknown"


def count_arg(text):
    n = int(text)
    if n < 1:
        raise argparse.ArgumentTypeError("the count must be at least 1")
    return n


def write(lines):
    RESULTS.write_text("\n".join(lines), encoding="utf-8")


def code(text):
    """`text` as Markdown inline code, whatever backticks it holds."""
    return f"`` {text} ``" if "`" in text else f"`{text}`"


def short(text, n=200):
    return text if len(text) <= n else text[:n] + f"... ({len(text)} characters)"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20261027)
    ap.add_argument("--count", type=count_arg, default=40000)
    ap.add_argument("--no-oracles", action="store_true",
                    help="compare with the model only, as tests/plant_bugs.py does")
    args = ap.parse_args()
    os.environ["PATH"] = f"{Path.home() / '.elan' / 'bin'}{os.pathsep}{os.environ.get('PATH', '')}"

    def give_up(why):
        write(["# Test results", "", "- Oracle: none ran", f"- Seed: {args.seed}", "- Inputs: 0",
               f"- Failures: 1 ({why})", ""])
        sys.exit(why)

    try:
        build = subprocess.run(["lake", "build", "path"], cwd=ROOT, capture_output=True,
                               text=True, errors="backslashreplace", timeout=BUILD_TIMEOUT)
        if build.returncode != 0:
            print(build.stdout + build.stderr)
            give_up("`lake build path` failed")
    except (OSError, subprocess.SubprocessError) as e:
        give_up(f"`lake build path` failed: {e}")

    failures = []

    # The model against Go's tests.
    go_right = 0
    for p, r in GO_CLEAN:
        ok = model_clean(p) == r and model_clean(r) == r
        go_right += ok
        if not ok:
            failures.append((f"the model on Go's cleantests {p!r}", repr(r), repr(model_clean(p))))
    for es, r in GO_JOIN:
        ok = model_join(es) == r
        go_right += ok
        if not ok:
            failures.append((f"the model on Go's jointests {es!r}", repr(r), repr(model_join(es))))

    cli = cli_cases()
    cli_right, cli_failures = run_cli(cli)
    failures += cli_failures

    oracles, left_out = [], []
    for name, setup in ORACLE_SETUPS:
        if args.no_oracles:
            left_out.append((name, "--no-oracles"))
            continue
        try:
            oracles.append(setup())
        except Exception as e:  # any oracle that cannot start is left out, and recorded
            left_out.append((name, str(e).splitlines()[0][:300] if str(e) else type(e).__name__))
    for name, why in left_out:
        print(f"oracle left out: {name}: {why}")

    items = list(inputs(args.seed, args.count))
    long_items = [it for it in items if it[0] == "long"]
    items = [it for it in items if it[0] != "long"]
    requests = [request(op, a) for _, op, a in items]
    lines = [r + ("\r\n" if i % 7 == 6 else "\n") for i, r in enumerate(requests)]
    out, problems = run_parallel([str(EXE), "serve"], lines + [m + "\n" for m in MALFORMED],
                                 JOBS)
    for problem in problems:
        failures.append(("(whole run)", "a clean run", problem))
    tool, malformed_out = out[:len(items)], out[len(items):]
    malformed_right = sum(1 for a in malformed_out if a == "error")
    for m, a in zip(MALFORMED, malformed_out):
        if model_line(m + "\n") != "error":
            failures.append((f"the model on {m!r}", "error", model_line(m + "\n")))
        if a != "error":
            failures.append((f"request {m!r}", "error", a))
    eof_right = 0
    for req, want in AT_EOF:
        if model_line(req) != want:
            failures.append((f"the model on {req!r} at end of input", want, model_line(req)))
        got, problem = run_lines([str(EXE), "serve"], [req], timeout=60)
        if got == [want] and not problem:
            eof_right += 1
        else:
            failures.append((repr(req) + " (at end of input)", want, f"{got} {problem or ''}".strip()))

    # The long inputs, one process, timed.
    long_lines = [request(op, a) + "\n" for _, op, a in long_items]
    start = time.monotonic()
    long_out, problem = run_lines([str(EXE), "serve"], long_lines)
    long_secs = time.monotonic() - start
    if problem or len(long_out) != len(long_lines):
        failures.append(("(long inputs)", "a clean run",
                         problem or f"{len(long_out)} answers for {len(long_lines)} requests"))
        long_out = (long_out + [""] * len(long_lines))[:len(long_lines)]
    long_chars = sum(sum(len(x) for x in a) for _, _, a in long_items)

    # The two parts of the model against each other: every path of the
    # exhaustive sets, Go's, Pike's, and the random paths.
    rng = random.Random(args.seed + 1)
    rules_checked = rules_agree = 0
    for _, op, a in items:
        if op == "clean":
            rules_checked += 1
            r, m = rules_clean(a[0], rng), model_clean(a[0])
            if r == m:
                rules_agree += 1
            else:
                failures.append((f"the model's two parts on {a[0]!r}", repr(r), repr(m)))

    # Against the model.
    wants = []
    differ_model = 0
    for (label, op, a), got in zip(items, tool):
        want = model(op, a)
        wants.append(want)
        if got != want:
            differ_model += 1
            failures.append((short(request(op, a)), short(want, 160), short(got, 160)))
    for (label, op, a), got in zip(long_items, long_out):
        want = model(op, a)
        if got != want:
            differ_model += 1
            failures.append((short(request(op, a)), short(want, 160), short(got, 160)))

    # Against the oracles: the same lines, the long ones too.
    all_items = items + long_items
    all_lines = lines + long_lines
    all_wants = wants + [model(op, a) for _, op, a in long_items]
    oracle_out = {}

    def ask(o):
        try:
            oracle_out[o.name] = o.answers(all_lines)
        except (RuntimeError, OSError) as e:
            oracle_out[o.name] = e

    threads = [threading.Thread(target=ask, args=(o,)) for o in oracles]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    for o in list(oracles):
        if isinstance(oracle_out[o.name], Exception):
            failures.append((f"({o.name} oracle run)", "a clean run", str(oracle_out[o.name])[:300]))
            oracles.remove(o)
    names = [o.name for o in oracles]
    asked = {o: 0 for o in names}
    agree = {o: 0 for o in names}
    by_op = {o: {} for o in names}
    named = {o: {} for o in names}
    for i, (label, op, a) in enumerate(all_items):
        want = all_wants[i]
        for o in names:
            theirs = oracle_out[o][i]
            if theirs == "n/a":
                continue
            asked[o] += 1
            by_op[o][op] = by_op[o].get(op, 0) + 1
            if theirs == want:
                agree[o] += 1
                continue
            reason = difference_reason(o, op, a, want, theirs)
            if reason is None:
                failures.append((f"{o}: {short(request(op, a))}", short(want, 160),
                                 short(theirs, 160)))
            else:
                n, example = named[o].get(reason, (0, None))
                named[o][reason] = (n + 1, example or request(op, a))

    by_label = {}
    for label, op, _ in items + long_items:
        key = f"{label} ({op})"
        by_label[key] = by_label.get(key, 0) + 1
    n_clean = sum(1 for _, op, _ in all_items if op == "clean")
    n_join = len(all_items) - n_clean

    lines_out = [
        "# Test results",
        "",
        "Written by `tests/run_tests.py`. Rerun it to check these numbers.",
        "",
        f"- Lean: {lean_version()}",
        "- Oracle: the model of Go's rules in `tests/run_tests.py`"
        + "".join(f"; {o.name}: {o.version}" for o in oracles),
    ]
    lines_out += [f"- {o.name}: {o.version}" for o in oracles]
    lines_out += [
        "- Oracles left out: " + ("; ".join(f"{n} ({why})" for n, why in left_out) or "none"),
        f"- Seed: {args.seed}",
        f"- Inputs: {len(all_items)}",
        "- By kind: " + ", ".join(f"{k} {n}" for k, n in by_label.items()),
        f"- Requests: `clean` {n_clean}, `join` {n_join}",
        f"- The model on Go's `cleantests` and `jointests`: {go_right} of "
        f"{len(GO_CLEAN) + len(GO_JOIN)}",
        f"- The model's two parts, the rules applied in a random order and the stack, agree on "
        f"{rules_agree} of {rules_checked} paths",
        f"- Answers that differ from the model: {differ_model}",
        f"- Long inputs: {len(long_items)}, {long_chars} characters in all, answered in "
        f"{long_secs:.1f} s by one `path serve`",
        "- Agreement with each oracle over the requests it answers: "
        + (", ".join(f"{o} {agree[o]} of {asked[o]}" for o in names) or "no oracle ran"),
        "- Requests each oracle answers, by operation: "
        + ("; ".join(f"{o}: " + ", ".join(f"{op} {n}" for op, n in sorted(by_op[o].items()))
                     for o in names) or "no oracle ran"),
        f"- Malformed requests answered `error`: {malformed_right} of {len(MALFORMED)}",
        f"- Requests ending in CR LF: every seventh, {sum(1 for l in lines if l.endswith(CRLF))}",
        f"- Last lines sent alone, with no LF, with CR LF, or with a lone CR, answered right: "
        f"{eof_right} of {len(AT_EOF)}",
        f"- Command-line modes (`clean`, `join`, and wrong arguments), printing and exiting as "
        f"the model says: {cli_right} of {len(cli)}",
        f"- Failures: {len(failures)}",
        "",
    ]
    if any(named[o] for o in names):
        lines_out += ["## Where the oracles differ", "",
                      "Each disagreement is counted under the reason the model confirms, with "
                      "the first input that showed it.", ""]
        for o in names:
            if not named[o]:
                continue
            lines_out += [f"### {o}", ""]
            for reason, (n, example) in sorted(named[o].items(), key=lambda kv: -kv[1][0]):
                lines_out.append(f"- {reason}: {n}; for example {code(short(example))}")
            lines_out.append("")
    if failures:
        lines_out += ["## Failures", "", "| Input | Expected | Got |", "|---|---|---|"]
        for what, want, got in failures[:200]:
            lines_out.append(f"| {code(what)} | {code(want)} | {code(got)} |")
        if len(failures) > 200:
            lines_out.append(f"| ... | {len(failures) - 200} more | |")
        lines_out.append("")
    write(lines_out)
    print(f"{len(all_items)} inputs, {len(failures)} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
