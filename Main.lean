/-
  Command line front end.

    semver check VERSION...

  prints, for each version, its printed form, or `invalid`, and exits
  with 1 when any is invalid.

    semver serve

  answers requests on standard input, one per line, for the
  differential tests. A string is sent as the hex digits of its UTF-8
  bytes, so that any character, a line break included, can be sent.

    parse HEX         prints  OK, then tab-separated: the printed form,
                      major, minor, patch, the pre-release identifiers
                      and the build identifiers; or REJECT. Each
                      pre-release identifier is `n:` and its number or
                      `a:` and its text, joined by `,`; the build
                      identifiers are joined by `,`.
    compare HEX HEX   prints  <, = or >, or REJECT when either string
                      is not a version

  A malformed request prints `error`: an unknown operation, hex digits
  that are not in pairs, or bytes that are not UTF-8. A request line
  may end in LF or CR LF.

  Every answer comes from the proved functions in `SemVer/`: `parse`,
  `Version.print` and `Version.compare`. The hex decoding and the
  request handling here are covered by the tests, not by a proof.
-/

import SemVer

open SemVer

def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def hexBytes : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let hi ← hexValue a
    let lo ← hexValue b
    let bs ← hexBytes rest
    pure ((hi * 16 + lo).toUInt8 :: bs)
  | [_] => none

/-- The string whose UTF-8 bytes the hex digits give. -/
def fromHex (h : String) : Option String := do
  let bs ← hexBytes h.toList
  String.fromUTF8? ⟨bs.toArray⟩

def identField : Ident → String
  | .num n => "n:" ++ toString n
  | .alnum s => "a:" ++ s

def fields (v : Version) : List String :=
  [v.print, toString v.major, toString v.minor, toString v.patch,
   ",".intercalate (v.pre.map identField), ",".intercalate v.build]

def showOrdering : Ordering → String
  | .lt => "<"
  | .eq => "="
  | .gt => ">"

/-- The answer to one request line, or `none` when it is malformed. -/
def request (line : String) : Option String :=
  match line.splitOn " " with
  | ["parse", h] => do
    let s ← fromHex h
    pure <| match parse s with
      | some v => "\t".intercalate ("OK" :: fields v)
      | none => "REJECT"
  | ["compare", ha, hb] => do
    let a ← fromHex ha
    let b ← fromHex hb
    pure <| match parse a, parse b with
      | some va, some vb => showOrdering (va.compare vb)
      | _, _ => "REJECT"
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

def check (args : List String) : IO UInt32 := do
  let mut code : UInt32 := 0
  for s in args do
    match parse s with
    | some v => IO.println v.print
    | none =>
      IO.println s!"invalid\t{s}"
      code := 1
  return code

def usage : String :=
  "usage: semver check VERSION...\n       semver serve"

def main (args : List String) : IO UInt32 := do
  match args with
  | "check" :: rest@(_ :: _) => check rest
  | ["serve"] => serve; return 0
  | _ => IO.eprintln usage; return 2
