# path: lexical path cleaning by Go's rules, proved

Programs clean a path before they use it: they drop `.`, let each `..` remove the name before it, and squeeze repeated slashes. A server that joins a path from a request to its own folder relies on that cleaning to keep the request inside the folder, and a mistake there lets a request read files outside it. Go's `path.Clean` gives the rules most often copied, from Rob Pike's "Lexical File Names in Plan 9". This library is those rules, and Go's `path.Join`, in Lean, proved to follow Go's documentation.

It only reads the string. It never looks at a file system, so it says nothing about symbolic links.

Machine-checked proofs show:

- **Clean is what Go's four rules give.** Go's documentation says Clean applies four rules "iteratively until no further processing can be done". Applied in any order until none applies, the rules leave the same elements, and `clean` gives them, written back as a path.
- **The result is clean.** It has no empty element and no `.`, and `..` only at its start, and none if the path is rooted. Cleaning it again changes nothing.
- **Join is what Go's documentation says**, and **joined paths stay inside.** A clean relative path with no `..`, joined to any folder, gives the folder's elements and then its own. Any path cleaned as a rooted path, `clean ("/" ++ u)`, and joined to a folder that is not the empty string, never leaves the folder.
- **Go's own tests** of Clean and Join give Go's results.

It is tested against a model of the rules and against Go, Python and Node; `tests/TEST-RESULTS.md` holds the record. It is a project of [Proven Commons](https://github.com/Proven-Commons/mission), built to the verified bar published there.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, so this is not verified.

## Use it

From Lean, on `String`:

- `Path.clean : String → String`;
- `Path.join : List String → String`.

`SPEC.md` says what each does.

## What is proved

The statements are in `Spec.lean`. The rules they use are in `Spec/Defs.lean`, written from Go's documentation, and the proofs are in `Proofs/`.

| Claim | Theorem |
|-------|---------|
| Whatever order Go's rules are applied in to the elements of a path, once none applies, the elements they leave are those of `clean p`. | `Spec.clean_rules` |
| The rules can always be applied until none applies, and they leave the elements of `clean p`. | `Spec.rules_end` |
| `clean p` names exactly one list of elements, as a path rooted exactly when `p` is; so, with `clean_rules`, whatever order the rules are applied in, once none applies they leave the same elements. | `Spec.clean_names` |
| The elements of `clean p` are some `..`, none if `p` is rooted, then names: no empty element and no `.`. | `Spec.clean_shape` |
| Cleaning a clean path changes nothing. | `Spec.clean_idem` |
| `join` leaves out empty elements, joins the rest with slashes and cleans them, and gives the empty string when nothing is left. | `Spec.join_eq` |
| A clean relative path with no `..`, joined to any path `b`, gives the elements of `clean b`, then its own. | `Spec.join_inside` |
| Any path cleaned as rooted, joined to a path `b` that is not the empty string (`.` and `/` are covered), gives the elements of `clean b`, then elements with no `..`. | `Spec.join_root_inside` |
| Go's tests of Clean, `cleantests`: each path cleans to its result, and the result to itself. Go's tests of Join, `jointests`. | `Spec.go_clean_tests`, `Spec.go_join_tests` |

## What is not proved

- **Go's code.** The proofs are against Go's documentation, written down in `Spec/Defs.lean`. That `clean` and `join` give what go1.24.7's `path.Clean` and `path.Join` give is tested (`tests/TEST-RESULTS.md`), not proved; only Go's own test tables are proved.
- **The file system.** The rules are lexical. If `b/x` is a symbolic link, `b/x/..` on the file system need not be `b`, and a link inside a folder can point outside it.
- **Two slashes at the start.** POSIX lets a system give `//` at the start of a path a meaning of its own. Go, and this library, read it as `/`; Python keeps it. That is a choice, recorded in `SPEC.md`.
- **That every order of the rules ends.** Each rule drops one element or two, as `Spec.Step` shows. This is read off the definition, not a statement, since bar item 3 asks every statement to mention `Path.clean`.
- **The empty string as the folder.** `join` leaves an empty element out, so `join ["", clean ("/" ++ u)]` is `clean ("/" ++ u)` itself (`join_eq`, `clean_idem`): a path from the root that `u` chooses, such as `/etc/passwd` for `u` = `../../etc/passwd`. `join_root_inside` needs `b ≠ ""`; pass `.` for the current folder, as Go's `http.Dir` does.
- **Other path functions** of Go: `Split`, `Base`, `Dir`, `Ext`, `IsAbs` and `Match`. Windows paths are not covered.
- **Strings that are not UTF-8.** Lean strings are Unicode text, so a Go string holding other octets cannot be passed to the library. On the command line, `path clean` and `path join` refuse an argument that is not UTF-8 with exit 2, since the Lean runtime would otherwise replace its ill-formed octets with U+FFFD and the tool would print a path Go would not; send such a path to `path serve` as hex, which answers `error` for it. The check reads the raw arguments from /proc/self/cmdline and is skipped where /proc is absent.
- **Time and memory.** No proof bounds them. `clean` reads the path once, as Go's loop does, and removes each character it writes at most once; the tests clean paths of a million characters.
- **Reading requests and printing answers in `Main.lean`.** The differential tests cover them.

## What you must trust

- The Lean kernel and the five external kernels shipped with Lean, which all check the proofs.
- `lake comparator`, which builds the statements and the proofs in a sandbox, exports them, and checks that each proof proves exactly its statement.
- bubblewrap and the Linux kernel's namespaces, which keep the untrusted build from tampering with that check.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about, such as natural number arithmetic and the conversion between strings and their characters.
- The operating system and hardware it runs on.
- For the tests only: the model in `tests/run_tests.py`, and the implementations it compares against. The record names their versions.

This project has no dependencies beyond Lean itself.

## Re-check it

Needs Linux, [elan](https://github.com/leanprover/elan), bubblewrap (`apt install bubblewrap`) and Python 3. The oracles also need Go and Node; the test script leaves out any it cannot start, and the record names them.

```
lake build
lake comparator --paranoid
python3 tests/run_tests.py
python3 tests/plant_bugs.py
```

`lake comparator --paranoid` builds the statements and the proofs in a sandbox. It checks that each theorem in `Proofs/` proves exactly the statement in `Spec.lean`, using only the axioms `propext`, `Classical.choice`, and `Quot.sound`, and replays it through every kernel shipped with Lean.

## Layout

- `Path/Basic.lean`: the code under proof, Go's loop written in Lean.
- `Spec.lean`: the statements, with `sorry` for proofs. A reviewer approves this file.
- `Spec/Defs.lean`: the rules the statements use, written from Go's documentation.
- `Proofs.lean` and `Proofs/`: the proofs.
- `Main.lean`: the command-line tool the tests drive.
- `lakefile.toml`: the build. It names the package and its version, its libraries and executable, and the default targets, and sets nothing else.
- `comparator.json`: which theorems `lake comparator` checks, and which axioms it allows.
- `bar.toml`: the record for the bar check: status, authors, approvals, and where things are.
- `SPEC.md`: the specification in plain words.
- `tests/`: the differential tests, the oracles, and the planted bugs.
