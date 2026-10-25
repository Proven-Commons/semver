/-
  The parser, reading a semantic version from a list of
  characters. Each reader returns the value it read and the
  characters left over, or `none` when the text breaks the
  grammar. The reader never reads past the end of its input.
-/

import Semver.Version

namespace Semver

/-- The longest run of digit characters at the front of the
    input, and what is left. -/
def takeDigits : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if isDigit c then
      let (a, b) := takeDigits cs
      (c :: a, b)
    else ([], c :: cs)

/-- The longest run of identifier characters at the front of the
    input, and what is left. -/
def takeIdChars : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if isIdChar c then
      let (a, b) := takeIdChars cs
      (c :: a, b)
    else ([], c :: cs)

/-- The value of a list of digit characters, most significant
    first. The caller checks that every character is a digit. -/
def digitsValue (ds : List Char) : Nat :=
  ds.foldl (fun a c => a * 10 + (c.toNat - 48)) 0

/-- The text of a number in the grammar: at least one digit, and
    no leading zero unless the text is the single digit 0. -/
def numTextOk (ds : List Char) : Bool :=
  !ds.isEmpty && ((ds.length == 1) || !(ds.head? == some '0'))

/-- Read one number of the grammar: a run of digits that passes
    the number text check. -/
def parseCoreNum (cs : List Char) : Option (Nat × List Char) :=
  let (ds, rest) := takeDigits cs
  if numTextOk ds then some (digitsValue ds, rest) else none

/-- Turn the text of one prerelease identifier into a value. A
    text of digits alone is a number, and must pass the number
    text check. Any other text is alphanumeric, as it stands. The
    caller checks that the text is not empty and holds only
    identifier characters. -/
def classifyPreId (ds : List Char) : Option PreId :=
  if ds.all isDigit then
    if numTextOk ds then some (.num (digitsValue ds)) else none
  else some (.alpha ds)

/-- Read one prerelease identifier: a nonempty run of identifier
    characters, classified by its text. -/
def parsePreId (cs : List Char) : Option (PreId × List Char) :=
  let (ds, rest) := takeIdChars cs
  if ds.isEmpty then none
  else match classifyPreId ds with
    | some id => some (id, rest)
    | none => none

/-- Read one build identifier: a nonempty run of identifier
    characters, held as text. Leading zeros are fine here. -/
def parseBuildId (cs : List Char) : Option (List Char × List Char) :=
  let (ds, rest) := takeIdChars cs
  if ds.isEmpty then none else some (ds, rest)

/-- Read a dot separated list of prerelease identifiers. The fuel
    is the length of the input plus one, which bounds the number
    of identifiers. After each identifier, a dot opens the next
    one; anything else ends the list. -/
def parsePreIdsGo : Nat → List Char → Option (List PreId × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    match parsePreId cs with
    | none => none
    | some (id, rest) =>
      if rest.head? = some '.' then
        match parsePreIdsGo fuel rest.tail with
        | some (ids, rest') => some (id :: ids, rest')
        | none => none
      else some ([id], rest)

/-- Read a dot separated list of build identifiers. -/
def parseBuildIdsGo : Nat → List Char → Option (List (List Char) × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    match parseBuildId cs with
    | none => none
    | some (id, rest) =>
      if rest.head? = some '.' then
        match parseBuildIdsGo fuel rest.tail with
        | some (ids, rest') => some (id :: ids, rest')
        | none => none
      else some ([id], rest)

/-- Read the prerelease part when a hyphen opens it. With no
    hyphen, the part is empty and nothing is read. -/
def parseOptPre (cs : List Char) : Option (List PreId × List Char) :=
  if cs.head? = some '-' then parsePreIdsGo (cs.tail.length + 1) cs.tail
  else some ([], cs)

/-- Read the build part when a plus sign opens it. -/
def parseOptBuild (cs : List Char) : Option (List (List Char) × List Char) :=
  if cs.head? = some '+' then parseBuildIdsGo (cs.tail.length + 1) cs.tail
  else some ([], cs)

/-- Read a dot where the grammar asks for one, returning what
    follows it. -/
def expectDot (cs : List Char) : Option (List Char) :=
  if cs.head? = some '.' then some cs.tail else none

/-- Read a whole version, returning the version and the characters
    left over. Three numbers split by dots, then the prerelease
    part, then the build part. -/
def parseVersion (cs : List Char) : Option (Version × List Char) :=
  (parseCoreNum cs).bind fun r₁ =>
  (expectDot r₁.2).bind fun rest₂ =>
  (parseCoreNum rest₂).bind fun r₂ =>
  (expectDot r₂.2).bind fun rest₄ =>
  (parseCoreNum rest₄).bind fun r₃ =>
  (parseOptPre r₃.2).bind fun r₄ =>
  (parseOptBuild r₄.2).bind fun r₅ =>
  some ({ major := r₁.1, minor := r₂.1, patch := r₃.1, pre := r₄.1,
          build := r₅.1 }, r₅.2)

/-- Parse a version from a character list. Anything after the
    version makes the text rejected, as does any grammar break. -/
def parse (cs : List Char) : Option Version :=
  match parseVersion cs with
  | some (v, []) => some v
  | _ => none

end Semver
