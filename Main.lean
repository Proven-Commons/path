/-
  Command line front end.

    path clean PATH
    path join ELEM...

  print the path cleaned, or the elements joined and cleaned, then a
  line end. `path join` with no elements, or only empty ones, prints an
  empty line. Wrong arguments exit with 2.

  The Lean runtime decodes each argument as UTF-8 before `main` sees
  it, and replaces ill-formed octets with U+FFFD. So `main` first reads
  the raw arguments from /proc/self/cmdline, and refuses with exit 2 if
  any of them is not UTF-8: Go would keep those octets, and the
  replaced string would give an answer Go does not. Such a path can be
  sent to `path serve` as hex. Where /proc is absent, the check is
  skipped.

    path serve

  answers requests on standard input, one per line, for the
  differential tests. A path is sent as the hex digits of its UTF-8
  octets, two per octet, and the empty path is written `-`.

    clean HEX           prints  OK and the hex of the path cleaned
                                                              (clean)
    join HEX...         prints  OK and the hex of the elements joined,
                                for zero or more elements     (join)

  A malformed request prints `error`: an unknown operation, a `clean`
  without exactly one path, hex digits that are not in pairs or not
  lower case, or octets that are not UTF-8. A request line may end in
  LF or CR LF.

  Every answer comes from the proved functions in `Path/`, applied to
  the arguments as `main` receives them. The hex coding, the argument
  check and the request handling here are covered by the tests, not by
  a proof.
-/

import Path

def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- Octets from hex digits in pairs. Tail recursive, so that long
    inputs do not use the stack. -/
def hexBytes (cs : List Char) (acc : ByteArray) : Option ByteArray :=
  match cs with
  | [] => some acc
  | a :: b :: rest =>
    match hexValue a, hexValue b with
    | some hi, some lo => hexBytes rest (acc.push (hi * 16 + lo).toUInt8)
    | _, _ => none
  | [_] => none

/-- The path a field gives: `-` for the empty path, else the hex of
    its UTF-8 octets. -/
def fromHex (f : String) : Option String :=
  if f = "-" then some ""
  else if f.isEmpty then none
  else do
    let bs ← hexBytes f.toList ByteArray.empty
    String.fromUTF8? bs

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

/-- The field for a path: `-` when it is empty. -/
def toHex (s : String) : String :=
  if s.isEmpty then "-"
  else String.ofList (s.toUTF8.toList.flatMap fun b =>
    [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

/-- The answer to one request line, or `none` when it is malformed. -/
def request (line : String) : Option String :=
  match line.splitOn " " with
  | ["clean", h] => do
    let p ← fromHex h
    pure s!"OK {toHex (Path.clean p)}"
  | "join" :: hs => do
    let es ← hs.mapM fromHex
    pure s!"OK {toHex (Path.join es)}"
  | _ => none

/-- The line without its line ending: LF, or CR LF. -/
def chomp (line : String) : String :=
  let cs := line.toList
  if cs.getLast? = some '\n' then
    let cs := cs.dropLast
    String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
  else line

def serve : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    stdout.putStrLn ((request (chomp line)).getD "error")
    stdout.flush

def usage : String :=
  "usage: path clean PATH\n       path join ELEM...\n       path serve"

/-- Whether every argument, as the process received it, is UTF-8.
    /proc/self/cmdline holds argv[0] and then each argument, each ended
    by a NUL. Without /proc, it answers `true`, as before this check. -/
def rawArgsUTF8 : IO Bool := do
  try
    let raw ← IO.FS.readBinFile "/proc/self/cmdline"
    let parts := (raw.toList.splitOn 0).drop 1
    pure (parts.all fun p => (String.fromUTF8? (ByteArray.mk p.toArray)).isSome)
  catch _ => pure true

def main (args : List String) : IO UInt32 := do
  unless (← rawArgsUTF8) do
    IO.eprintln "path: an argument is not UTF-8; send it to `path serve` as hex"
    return 2
  match args with
  | ["clean", p] => IO.println (Path.clean p); return 0
  | "join" :: es => IO.println (Path.join es); return 0
  | ["serve"] => serve; return 0
  | _ => IO.eprintln usage; return 2
