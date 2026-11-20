# Planted bugs

Written by `tests/plant_bugs.py`. Each bug is a change of one line, or of two, to `Path/Basic.lean` unless it names `Main.lean`, tested with `tests/run_tests.py --count 1000 --no-oracles`, which builds only the executable and compares it with the model alone. Every bug must give failures, and the unchanged code none. A bug that does not build, or a run that gives up or dies, counts as missed.

| Planted bug | Failures |
|---|---|
| none | 0 |
| backtracking removes one character more, past `dotdot` | 1281 |
| backtracking does not stop at a slash | 2121 |
| `..` backtracks when the output is no longer than `dotdot` | 4842 |
| a `..` that cannot backtrack is kept in a rooted path, not in one that is not | 6537 |
| `dotdot` does not move past a `..` that is kept | 289 |
| a kept `..` gets a slash before it even at the start | 4426 |
| a `.` at the end is kept | 10537 |
| a `..` at the end is dropped | 3410 |
| a `.` before a slash is copied as a name | 29229 |
| in a rooted path, the first name gets a slash after the root | 32251 |
| a name runs on past the slash after it | 68609 |
| the length is not counted while a name is copied | 3347 |
| the root's `dotdot` is 0, so a `..` can remove the root | 1653 |
| the root alone is not rooted | 15 |
| an empty result is the empty string, not `.` | 2320 |
| `join` of only empty elements gives `.` | 129 |
| `join` keeps the empty elements before the first other one | 82 |
| Main.lean: `-` is read as the path `-` | 357 |
| Main.lean: `clean` takes more than one field | 2 |
| Main.lean: a CR before the LF is kept | 15536 |
| Main.lean: `path clean` prints the path as given | 4 |
| Main.lean: wrong arguments exit with 0 | 6 |

Bugs caught: 22 of 22
