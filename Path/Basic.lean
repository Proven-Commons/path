/-
  Lexical path cleaning, as Go's `path.Clean` and `path.Join` do it
  (go1.24.7, src/path/path.go). The loop below follows Go's line by
  line. Go writes into a buffer and keeps its length `w`; here the
  buffer is a list, kept reversed so that writing and removing at the
  end take one step, and `w` is its length. Go reads the input by
  index; here the loop takes the input apart from the front, so it
  reads each character once.
-/

namespace Path

/-- The part of Go's `..` case that backtracks. Go first removes one
    character, then removes more while the output is longer than
    `dotdot` and the character it last removed is not a slash. `out`
    is the output, reversed, and `w` its length. -/
def backtrack (dotdot : Nat) : List Char → Nat → List Char × Nat
  | c :: out, w + 1 => if w > dotdot ∧ c ≠ '/' then backtrack dotdot out w else (out, w)
  | out, w => (out, w)

/-- Go's `..` case. If the output is longer than `dotdot`, it can
    backtrack. Otherwise, in a path that is not rooted, it writes `..`,
    after a slash when the output is not empty, and that is now where
    `..` must stop. Gives the output, its length and the new `dotdot`. -/
def parent (rooted : Bool) (dotdot : Nat) (out : List Char) (w : Nat) :
    List Char × Nat × Nat :=
  if w > dotdot then
    let (out, w) := backtrack dotdot out w
    (out, w, dotdot)
  else if !rooted then
    let (out, w) := if w > 0 then ('/' :: out, w + 1) else (out, w)
    ('.' :: '.' :: out, w + 2, w + 2)
  else (out, w, dotdot)

mutual
/-- Go's loop, at the start of a path element. -/
def loop (rooted : Bool) (dotdot : Nat) (out : List Char) (w : Nat) :
    List Char → List Char × Nat
  | [] => (out, w)
  -- empty path element
  | '/' :: rest => loop rooted dotdot out w rest
  -- . element
  | ['.'] => (out, w)
  | '.' :: rest@('/' :: _) => loop rooted dotdot out w rest
  -- .. element: remove to last /
  | ['.', '.'] =>
    let (out, w, _) := parent rooted dotdot out w
    (out, w)
  | '.' :: '.' :: rest@('/' :: _) =>
    let (out, w, dotdot) := parent rooted dotdot out w
    loop rooted dotdot out w rest
  -- real path element: add a slash if needed, then copy the element
  | c :: rest =>
    let (out, w) :=
      if rooted && w != 1 || !rooted && w != 0 then ('/' :: out, w + 1) else (out, w)
    copy rooted dotdot (c :: out) (w + 1) rest

/-- The rest of a real path element, up to the next slash. Go stops
    before the slash and its loop then skips it; here `copy` skips it. -/
def copy (rooted : Bool) (dotdot : Nat) (out : List Char) (w : Nat) :
    List Char → List Char × Nat
  | [] => (out, w)
  | '/' :: rest => loop rooted dotdot out w rest
  | c :: rest => copy rooted dotdot (c :: out) (w + 1) rest
end

/-- `Clean` on the characters of a path. -/
def cleanChars (path : List Char) : List Char :=
  match path with
  | [] => ['.']
  | c :: rest =>
    let rooted := c == '/'
    let (out, w) := if rooted then loop true 1 ['/'] 1 rest else loop false 0 [] 0 path
    -- Turn empty string into "."
    if w == 0 then ['.'] else out.reverse

/-- The path cleaned by lexical processing alone, as Go's `path.Clean`
    cleans it. -/
def clean (path : String) : String :=
  String.ofList (cleanChars path.toList)

/-- Go's `path.Join`: the elements, the empty ones before the first
    other one left out, separated by slashes, and cleaned. If there are
    no elements, or all are empty, it gives the empty string. -/
def join (elem : List String) : String :=
  if elem.all (·.isEmpty) then ""
  else clean ("/".intercalate (elem.dropWhile (·.isEmpty)))

end Path
