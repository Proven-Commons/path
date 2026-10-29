/-
  The rules of Go's `path.Clean`, written from its documentation
  (https://pkg.go.dev/path#Clean, go1.24.7):

    Clean returns the shortest path name equivalent to path by purely
    lexical processing. It applies the following rules iteratively
    until no further processing can be done:

     1. Replace multiple slashes with a single slash.
     2. Eliminate each . path name element (the current directory).
     3. Eliminate each inner .. path name element (the parent
        directory) along with the non-.. element that precedes it.
     4. Eliminate .. elements that begin a rooted path: that is,
        replace "/.." by "/" at the beginning of a path.

    The returned path ends in a slash only if it is the root "/".

    If the result of this process is an empty string, Clean returns
    the string ".".

  and from Rob Pike, "Lexical File Names in Plan 9, or Getting Dot-Dot
  Right" (https://9p.io/sys/doc/lexnames.html), which it cites.

  The rules are stated here on the elements of a path, the pieces
  between its slashes. A path is rooted when it starts with a slash.
  The root is kept apart, so the elements of `/a/b` are the empty
  element before the first slash, `a` and `b`, and the path is rooted.
  An empty element comes from two slashes in a row, from the slash of
  a rooted path, or from a slash at the end. Rule 1 and the sentence
  on a slash at the end both say the same of elements: an empty element
  is dropped.

  This file uses nothing from the code.
-/

namespace Spec

/-- A path element: the characters between two slashes. -/
abbrev Element := List Char

/-- The element `.`. -/
def dot : Element := ['.']

/-- The element `..`. -/
def dotdot : Element := ['.', '.']

/-- `es` are the elements of the path `p`: `p` is the elements with a
    slash between each two, and no element holds a slash. There is at
    least one element; the path "" has the one element "". -/
def Splits (p : List Char) (es : List Element) : Prop :=
  es ≠ [] ∧ p = List.intercalate ['/'] es ∧ ∀ e ∈ es, '/' ∉ e

/-- A path is rooted when it starts with a slash. -/
def Rooted (p : List Char) : Bool :=
  p.head? == some '/'

/-- One rule, applied once, to the elements of a path that is `rooted`
    or not. -/
inductive Step (rooted : Bool) : List Element → List Element → Prop
  /-- Rule 1, with the sentence on a slash at the end: drop an empty
      element. -/
  | empty (xs ys : List Element) : Step rooted (xs ++ [] :: ys) (xs ++ ys)
  /-- Rule 2: drop a `.` element. -/
  | dot (xs ys : List Element) : Step rooted (xs ++ dot :: ys) (xs ++ ys)
  /-- Rule 3: drop a `..` element and the element before it, when that
      is a name: not empty, not `.` and not `..`. Go's words are "the
      non-.. element that precedes it". Read literally, with an empty
      element or a `.` allowed there, the rules would end in more than one
      place: `abc/./../def` could end as `abc/def` or `def`, and Go's own
      tests give `def`. An empty element or a `.` before the `..` is
      dropped first, by rule 1 or 2. -/
  | parent (xs : List Element) (e : Element) (ys : List Element) :
      e ≠ [] → e ≠ dot → e ≠ dotdot →
      Step rooted (xs ++ e :: dotdot :: ys) (xs ++ ys)
  /-- Rule 4: drop a `..` element at the start of a rooted path. -/
  | root (ys : List Element) : rooted = true → Step rooted (dotdot :: ys) ys

/-- The rules, applied any number of times, in any order. -/
inductive Steps (rooted : Bool) : List Element → List Element → Prop
  | refl (es : List Element) : Steps rooted es es
  | step {es es' es'' : List Element} :
      Step rooted es es' → Steps rooted es' es'' → Steps rooted es es''

/-- No rule applies: "no further processing can be done". -/
def Normal (rooted : Bool) (es : List Element) : Prop :=
  ∀ es', ¬ Step rooted es es'

/-- The path with these elements: a slash first when it is rooted, a
    slash between each two elements, and `.` for no elements in a path
    that is not rooted. When no element is empty, as when no rule
    applies, it ends in a slash only when it is the root `/`. -/
def render (rooted : Bool) (es : List Element) : List Char :=
  if rooted then '/' :: List.intercalate ['/'] es
  else if es = [] then dot
  else List.intercalate ['/'] es

/-- `s` is the path, rooted or not, with the elements `es`: no element
    holds a slash, and no rule applies to them. -/
def Names (s : String) (rooted : Bool) (es : List Element) : Prop :=
  s.toList = render rooted es ∧ Normal rooted es ∧ ∀ e ∈ es, '/' ∉ e

end Spec
