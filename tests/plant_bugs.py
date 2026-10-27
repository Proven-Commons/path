#!/usr/bin/env python3
"""Check that the differential tests catch planted bugs.

Each bug is a change of one line, or of two, to Path/Basic.lean, or to
Main.lean where its description says so. The script copies the
project to a temporary folder, plants one bug at a time, runs
tests/run_tests.py there with a small count and without the oracles,
and records how many failures the tests report. So every failure
counted is the tool disagreeing with the model of Go's rules; an
oracle that crashes or times out cannot pass for a catch. Every
planted bug must give at least one failure. The unchanged copy must
give none. A bug that stops the executable from building is not a
catch: the tests then give up, and the bug counts as missed. So is any
run that gives up (its record shows `- Failures: 1 (why)`), a run that
dies without writing its record, and one whose exit status does not
match the failures it records. The tests build only the executable
(`lake build path`), so a bug that breaks a proof still runs.

    python3 tests/plant_bugs.py [--count N]

The script writes tests/PLANTED-BUGS.md and exits non-zero if any bug
goes uncaught.
"""

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / "tests" / "PLANTED-BUGS.md"
CODE = "Path/Basic.lean"

# (what the bug does, the text as written, the text with the bug[, file])
BUGS = [
    ("backtracking removes one character more, past `dotdot`",
     "  | c :: out, w + 1 => if w > dotdot ∧ c ≠ '/' then backtrack dotdot out w else (out, w)",
     "  | c :: out, w + 1 => if w ≥ dotdot ∧ c ≠ '/' then backtrack dotdot out w else (out, w)"),
    ("backtracking does not stop at a slash",
     "  | c :: out, w + 1 => if w > dotdot ∧ c ≠ '/' then backtrack dotdot out w else (out, w)",
     "  | c :: out, w + 1 => if w > dotdot then backtrack dotdot out w else (out, w)"),
    ("`..` backtracks when the output is no longer than `dotdot`",
     "  if w > dotdot then\n",
     "  if w ≥ dotdot then\n"),
    ("a `..` that cannot backtrack is kept in a rooted path, not in one that is not",
     "  else if !rooted then",
     "  else if rooted then"),
    ("`dotdot` does not move past a `..` that is kept",
     "    ('.' :: '.' :: out, w + 2, w + 2)",
     "    ('.' :: '.' :: out, w + 2, dotdot)"),
    ("a kept `..` gets a slash before it even at the start",
     "    let (out, w) := if w > 0 then ('/' :: out, w + 1) else (out, w)",
     "    let (out, w) := if w ≥ 0 then ('/' :: out, w + 1) else (out, w)"),
    ("a `.` at the end is kept",
     "  | ['.'] => (out, w)",
     "  | ['.'] => ('.' :: out, w + 1)"),
    ("a `..` at the end is dropped",
     "    let (out, w, _) := parent rooted dotdot out w",
     "    let (out, w, _) := (out, w, dotdot)"),
    ("a `.` before a slash is copied as a name",
     "  | '.' :: rest@('/' :: _) => loop rooted dotdot out w rest",
     "  | '.' :: rest@('/' :: _) => copy rooted dotdot ('.' :: out) (w + 1) rest"),
    ("in a rooted path, the first name gets a slash after the root",
     "      if rooted && w != 1 || !rooted && w != 0 then ('/' :: out, w + 1) else (out, w)",
     "      if rooted && w != 0 || !rooted && w != 0 then ('/' :: out, w + 1) else (out, w)"),
    ("a name runs on past the slash after it",
     "  | [] => (out, w)\n  | '/' :: rest => loop rooted dotdot out w rest",
     "  | [] => (out, w)\n  | '/' :: rest => copy rooted dotdot ('/' :: out) (w + 1) rest"),
    ("the length is not counted while a name is copied",
     "  | c :: rest => copy rooted dotdot (c :: out) (w + 1) rest",
     "  | c :: rest => copy rooted dotdot (c :: out) w rest"),
    ("the root's `dotdot` is 0, so a `..` can remove the root",
     "    let (out, w) := if rooted then loop true 1 ['/'] 1 rest else loop false 0 [] 0 path",
     "    let (out, w) := if rooted then loop true 0 ['/'] 1 rest else loop false 0 [] 0 path"),
    ("the root alone is not rooted",
     "    let rooted := c == '/'",
     "    let rooted := c == '/' && rest != []"),
    ("an empty result is the empty string, not `.`",
     "    if w == 0 then ['.'] else out.reverse",
     "    if w == 0 then [] else out.reverse"),
    ("`join` of only empty elements gives `.`",
     "  if elem.all (·.isEmpty) then \"\"",
     "  if elem.all (·.isEmpty) then \".\""),
    ("`join` keeps the empty elements before the first other one",
     "  else clean (\"/\".intercalate (elem.dropWhile (·.isEmpty)))",
     "  else clean (\"/\".intercalate elem)"),
    ("Main.lean: `-` is read as the path `-`",
     "  if f = \"-\" then some \"\"",
     "  if f = \"-\" then some \"-\"",
     "Main.lean"),
    ("Main.lean: `clean` takes more than one field",
     "  | [\"clean\", h] => do",
     "  | \"clean\" :: h :: _ => do",
     "Main.lean"),
    ("Main.lean: a CR before the LF is kept",
     "    String.ofList (if cs.getLast? = some '\\r' then cs.dropLast else cs)",
     "    String.ofList cs",
     "Main.lean"),
    ("Main.lean: `path clean` prints the path as given",
     "  | [\"clean\", p] => IO.println (Path.clean p); return 0",
     "  | [\"clean\", p] => IO.println p; return 0",
     "Main.lean"),
    ("Main.lean: wrong arguments exit with 0",
     "  | _ => IO.eprintln usage; return 2",
     "  | _ => IO.eprintln usage; return 0",
     "Main.lean"),
]


def failures(copy, count):
    """The failures a run of the tests reports, or None, with the run's
    output, when it reports none: the code did not build, or the run did
    not finish. A run that dies writes no record, so the old one is
    removed first rather than read again."""
    record = copy / "tests" / "TEST-RESULTS.md"
    record.unlink(missing_ok=True)
    run = subprocess.run([sys.executable, "tests/run_tests.py", "--count", str(count),
                          "--no-oracles"],
                         cwd=copy, capture_output=True, text=True)
    out = run.stdout + run.stderr
    if not record.exists():
        return None, f"no record written, exit status {run.returncode}\n{out}"
    m = re.search(r"^- Failures: (\d+)(.*)$", record.read_text(encoding="utf-8"), re.M)
    if m is None or m.group(2).strip():
        return None, out  # the run gave up, for example the bug did not build: not a catch
    n = int(m.group(1))
    if run.returncode != (1 if n else 0):
        return None, f"{n} failures but exit status {run.returncode}\n{out}"
    return n, None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=1000)
    args = ap.parse_args()
    rows, missed = [], 0
    with tempfile.TemporaryDirectory() as tmp:
        copy = Path(tmp) / "path"
        shutil.copytree(ROOT, copy, symlinks=True,
                        ignore=shutil.ignore_patterns("PLANTED-BUGS.md", "__pycache__"))
        n, err = failures(copy, args.count)
        rows.append(("none", n))
        if n != 0:
            missed += 1
        print(f"none: {n} failures" + (" (did not build or did not finish)" if err else ""),
              flush=True)
        for what, line, bug, *where in BUGS:
            name = where[0] if where else CODE
            code = copy / name
            original = code.read_text(encoding="utf-8")
            if original.count(line) != 1:
                sys.exit(f"{name} no longer holds, once, the text for {what!r}: {line}")
            code.write_text(original.replace(line, bug), encoding="utf-8")
            n, err = failures(copy, args.count)
            code.write_text(original, encoding="utf-8")
            rows.append((what, n))
            if not n:
                missed += 1
            print(f"{what}: {n} failures" + (" (did not build or did not finish)" if err else ""),
                  flush=True)
            if err:
                print(err[-2000:], flush=True)
    lines = ["# Planted bugs", "",
             "Written by `tests/plant_bugs.py`. Each bug is a change of one line, or of two, "
             f"to `{CODE}` unless it names `Main.lean`, tested with "
             f"`tests/run_tests.py --count {args.count} --no-oracles`, which builds only the "
             "executable and compares it with the model alone. Every bug must give failures, "
             "and the unchanged code none. A bug that does not build, or a run that gives up "
             "or dies, counts as missed.", "",
             "| Planted bug | Failures |", "|---|---|"]
    lines += [f"| {what} | {'did not build or did not finish' if n is None else n} |"
              for what, n in rows]
    lines += ["", f"Bugs caught: {sum(1 for what, n in rows[1:] if n)} of {len(BUGS)}", ""]
    RECORD.write_text("\n".join(lines), encoding="utf-8")
    return 1 if missed else 0


if __name__ == "__main__":
    sys.exit(main())
