/-
  Command line front end.

    path clean PATH
    path join ELEM...

  print the path cleaned, or the elements joined and cleaned, then a
  line end. `path join` with no elements, or only empty ones, prints an
  empty line. Wrong arguments exit with 2.

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

  Every answer comes from the proved functions in `Path/`. The hex
  coding and the request handling here are covered by the tests, not by
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

def main (args : List String) : IO UInt32 := do
  match args with
  | ["clean", p] => IO.println (Path.clean p); return 0
  | "join" :: es => IO.println (Path.join es); return 0
  | ["serve"] => serve; return 0
  | _ => IO.eprintln usage; return 2
