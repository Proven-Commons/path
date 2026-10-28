# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Oracle: the model of Go's rules in `tests/run_tests.py`; Go: `path.Clean` and `path.Join` of the standard library of go version go1.24.7 linux/amd64; Python: `posixpath.normpath` of Python 3.13.17; Node: `path.posix.normalize` and `path.posix.join` of Node v22.22.0
- Go: `path.Clean` and `path.Join` of the standard library of go version go1.24.7 linux/amd64
- Python: `posixpath.normpath` of Python 3.13.17
- Node: `path.posix.normalize` and `path.posix.join` of Node v22.22.0
- Oracles left out: none
- Seed: 20261027
- Inputs: 167263
- By kind: Go cleantests (clean) 36, Go cleantests, the result (clean) 36, Go jointests (join) 11, an empty first element, a rooted second (join) 1, Pike, and edges (clean) 29, every path over a . / up to 10 (clean) 88573, every path over a b . / up to 7 (clean) 18565, random path (clean) 40000, random join (join) 20000, long (clean) 11, long (join) 1
- Requests: `clean` 147250, `join` 20013
- The model on Go's `cleantests` and `jointests`: 47 of 47
- The model's two parts, the rules applied in a random order and the stack, agree on 147239 of 147239 paths
- Answers that differ from the model: 0
- Long inputs: 12, 12296441 characters in all, answered in 2.8 s by one `path serve`
- Agreement with each oracle over the requests it answers: Go 167263 of 167263, Python 138020 of 147250, Node 117446 of 167263
- Requests each oracle answers, by operation: Go: clean 147250, join 20013; Python: clean 147250; Node: clean 147250, join 20013
- Malformed requests answered `error`: 31 of 31
- Requests ending in CR LF: every seventh, 23893
- Last lines sent alone, with no LF, with CR LF, or with a lone CR, answered right: 4 of 4
- Command-line modes (`clean`, `join`, and wrong arguments), printing and exiting as the model says: 21 of 21
- Failures: 0

## Where the oracles differ

Each disagreement is counted under the reason the model confirms, with the first input that showed it.

### Python

- Python keeps two slashes at the start of a path, as POSIX allows: 9230; for example `clean 2f2f616263`

### Node

- Node keeps a slash at the end of a path: 41482; for example `clean 6162632f`
- Node's `join` gives `.` when every element is empty, or there are none: 5099; for example `join`
- Node keeps a slash at the end of a path (in `join`): 3236; for example `join 612f -`
