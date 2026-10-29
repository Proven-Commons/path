# Specification: path

Go's documentation of `path.Clean` (https://pkg.go.dev/path#Clean) says it gives "the shortest path name equivalent to path by purely lexical processing". It reads only the string: it never looks at a file system. This library cleans paths by the rules of that documentation, and joins them as `path.Join` does, in Lean, on strings. That the result is the shortest such path is Go's description; it is not a statement here.

A reviewer who did not write this specification approves it. The approval also covers `Spec.lean`, `Spec/Defs.lean`, and the other files that `bar.toml` lists.

## Elements

`Spec/Defs.lean` states Go's rules on the elements of a path: the pieces between its slashes. `Spec.Splits p es` says that `p` is the elements `es` with a slash between each two, and that no element holds a slash. A path has at least one element; the empty path has the one empty element.

A path is rooted when it starts with a slash (`Spec.Rooted`). The root is kept apart from the elements, so `/a/b` is rooted, with the elements "", `a` and `b`. An empty element comes from two slashes in a row, from the slash of a rooted path, or from a slash at the end.

## The rules

Go's documentation says that Clean "applies the following rules iteratively until no further processing can be done":

1. Replace multiple slashes with a single slash.
2. Eliminate each `.` path name element (the current directory).
3. Eliminate each inner `..` path name element (the parent directory) along with the non-`..` element that precedes it.
4. Eliminate `..` elements that begin a rooted path: that is, replace `/..` by `/` at the beginning of a path.

It adds: "The returned path ends in a slash only if it is the root `/`", and "If the result of this process is an empty string, Clean returns the string `.`".

`Spec.Step` is one rule, applied once, to the elements:

- **Rule 1** drops an empty element. On elements, rule 1 and the sentence on a slash at the end say the same thing.
- **Rule 2** drops a `.` element.
- **Rule 3** drops a `..` element and the element before it, when that is a name: not empty, not `.` and not `..`. An empty element or a `.` before the `..` is dropped first, by rule 1 or 2. Go's words are "the non-`..` element that precedes it"; read literally, with an empty element or a `.` allowed there, the rules would end in more than one place. `abc/./../def` could end as `abc/def` or as `def`, and Go's own tests give `def`.
- **Rule 4** drops a `..` at the start of a rooted path.

`Spec.Steps` is the rules applied any number of times, in any order. `Spec.Normal` says that no rule applies. `Spec.render` writes elements back as a path: a slash first when it is rooted, a slash between each two elements, and `.` for no elements in a path that is not rooted. So, when no element is empty, as for the elements of `clean p` (`clean_shape`), the result ends in a slash only when it is the root `/`.

**Clean** is the path `render` writes for the elements the rules leave, in whatever order they are applied (`clean_rules`), and the rules can always be applied until none applies (`rules_end`). `Spec.Names s r es` says that `s` is the path `render r` writes for `es`, that no rule applies to `es`, and that no element of `es` holds a slash; `clean p` names exactly one such list (`clean_names`). So every order of the rules ends at the same elements. Each rule drops one element or two, as `Spec.Step` shows, so the rules always come to an end.

The elements of `clean p` are some `..`, none if `p` is rooted, and then names (`clean_shape`). So the result of `clean` has no empty element and no `.`, and `..` only at its start, and none if it is rooted. It is rooted exactly when the path was (`clean_names`). Cleaning it again changes nothing (`clean_idem`).

**Two slashes at the start.** POSIX says that "a pathname that begins with two successive slashes may be interpreted in an implementation-defined manner". Go reads them as one slash, and so does this library: `//abc` cleans to `/abc`, as in Go's own tests. Python's `posixpath.normpath` keeps exactly two.

## Join

Go's documentation: "Join joins any number of path elements into a single path, separating them with slashes. Empty elements are ignored. The result is Cleaned. However, if the argument list is empty or all its elements are empty, Join returns an empty string." `join_eq` states this.

**Joined paths stay inside.** A clean relative path `q` with no `..`, joined to any path `b`, gives the elements of `clean b` and then those of `q` (`join_inside`). Any path `u`, cleaned as a rooted path (`clean ("/" ++ u)`) and joined to a path `b` that is not the empty string (`.` and `/` are covered), gives the elements of `clean b` and then elements with no `..` (`join_root_inside`). If `b` is the empty string, `join` leaves it out, and the result is rooted: `join ["", "/etc"]` is `/etc`.

"Inside" is lexical: it says what the strings are, not where a file system resolves them. A symbolic link inside `b` can point anywhere.

## What must always hold

Each property is a theorem in `Spec.lean`, under the name given.

| Property | Theorem |
|----------|---------|
| Whatever order the rules are applied in, once none applies, the elements left are those of `clean p`. | `Spec.clean_rules` |
| The rules can always be applied until none applies, and leave the elements of `clean p`. | `Spec.rules_end` |
| `clean p` names exactly one list of elements, rooted when `p` is. | `Spec.clean_names` |
| The elements of `clean p` are some `..` (none if rooted), then names. | `Spec.clean_shape` |
| Cleaning a clean path changes nothing. | `Spec.clean_idem` |
| `join` is what Go's documentation says. | `Spec.join_eq` |
| A clean relative path with no `..`, joined to `b`, adds its elements to those of `clean b`. | `Spec.join_inside` |
| Any path cleaned as rooted, joined to a `b` that is not the empty string (`.` and `/` are covered), adds elements with no `..` to those of `clean b`. | `Spec.join_root_inside` |
| Go's tests of Clean, each path and each result. | `Spec.go_clean_tests` |
| Go's tests of Join, and an empty first element joined to a rooted path. | `Spec.go_join_tests` |

## Strings

The functions take and give Lean strings, which are Unicode text in UTF-8. Go's strings may hold any octets. The rules look only at `/` and `.`, which are single octets in UTF-8 and never part of another character, so Go should give the same answer on UTF-8 text; the tests check this with characters that are not ASCII. A Go string that is not UTF-8 cannot be passed to this library.

## The command-line tool

`Main.lean` has these modes:

- `path clean PATH` prints the path cleaned.
- `path join ELEM...` prints the elements joined and cleaned, and an empty line for no elements or only empty ones.
- `path serve` answers requests from the differential tests, one per line. The header comment of `Main.lean` gives the protocol.

Wrong arguments exit with 2. Every answer comes from the functions above. An argument of `clean` or `join` that is not UTF-8 is refused with exit 2: the Lean runtime would replace its ill-formed octets with U+FFFD, and the tool would print a path Go would not. Such a path can be sent to `path serve` as hex, which answers `error` for it. The tool reads the raw arguments from /proc/self/cmdline for this check, and skips it where /proc is absent.
