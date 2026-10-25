# Specification: semver

A Semantic Versioning 2.0.0 parser, printer, and precedence comparison in Lean, following the specification at semver.org. A reviewer who did not write this specification approves it, together with any statement file a reviewer adds later. No such file exists yet, so nothing here counts toward the verified bar yet.

Text is `List Char`. A Lean `Char` is one Unicode scalar value.

## Values

One value type, `Version`:

- `major`, `minor`, `patch`: natural numbers.
- `pre`: a list of prerelease identifiers. Each identifier is `num n`, a number held as the number itself, or `alpha cs`, a text held as its characters.
- `build`: a list of build identifiers, each a list of characters held as text.

Two choices in this shape carry weight:

- A numeric prerelease identifier is held as a number, never as text. So the type cannot hold a numeric identifier with a leading zero, and cannot hold an alphanumeric identifier whose text is all digits: such a text is a number here. An `alpha` identifier is only well formed when its text holds at least one character that is not a digit. That rule is what lets a printed identifier always read back as the same kind.
- Build identifiers are held as text and never turned into numbers. Leading zeros in build metadata are part of the text, and build metadata takes no part in precedence, so nothing is gained by reading it as a number.

## The grammar

A version text is the core, then an optional prerelease part, then an optional build part. Anything after the build part, and any input that ends early, is rejected.

- The core is three numbers split by dots. A number is a run of digits with no leading zero: the text `0` is fine, the text `01` is not. An empty part and a part with a non-digit are rejected.
- The prerelease part opens with a hyphen. It is a list of identifiers split by dots. An identifier is a nonempty run of digits, ASCII letters, and hyphens. An identifier made only of digits is numeric and must pass the same no-leading-zero rule. Any other identifier is alphanumeric.
- The build part opens with a plus sign. It is a list of identifiers split by dots, of the same character set. Identifiers must not be empty. Leading zeros are allowed.

## The printer

The printer writes the canonical text: numbers in decimal with no leading zeros, prerelease identifiers as their number or their text, build identifiers as their text, parts joined by dots, a hyphen before the prerelease part when there is one, a plus sign before the build part when there is one.

## Precedence

`compare` follows section 11 of the specification:

1. Compare major, then minor, then patch, by value.
2. When the cores are equal, a version with a prerelease is lower than the same version without one.
3. Two prereleases compare identifier by identifier. Numeric identifiers compare by value. Alphanumeric identifiers compare in ASCII order. A numeric identifier is lower than an alphanumeric one. When every shared identifier is equal, the shorter list is lower.
4. Build metadata takes no part.

## The claims

Three claims are proved, for the value type as defined here:

- The round trip: for every well formed version, parsing its printed form gives the version back. Well formed means each `alpha` identifier is nonempty, holds only identifier characters, and holds a character that is not a digit, and each build identifier is nonempty and holds only identifier characters. Numbers and numeric identifiers need no condition: a natural number prints canonically by construction.
- A version compares equal to itself.
- Two versions that agree on the three numbers and the prerelease compare equal, whatever their build metadata. In particular, changing only the build metadata of a version leaves it comparing equal to the original.

The section 11 example chain is also proved, step by step, as example cases:

1.0.0-alpha < 1.0.0-alpha.1 < 1.0.0-alpha.beta < 1.0.0-beta < 1.0.0-beta.2 < 1.0.0-beta.11 < 1.0.0-rc.1 < 1.0.0

No claim is made that the parser accepts every text the grammar allows, or rejects every text it forbids, beyond what the round trip needs. The test harness checks that behaviour against an oracle written from this specification's source text, Semantic Versioning 2.0.0, and the results file records the outcome. No claim is made that `compare` is a full order on all versions: transitivity and totality are not proved. Nothing here speaks of version ranges, sorting, or choosing among versions.

## The command-line tool

`Main.lean` reads one request per line and prints one answer per line. A request is an operation word, then optionally one space and comma-separated decimal character codes.

- `parse` takes the codes of one version text. The answer is `ok:` followed by the codes of the canonical print of the parsed version, or `none` when the text is rejected. With no codes, the input is empty and the answer is `none`.
- `cmp` takes the codes of two version texts split by one code 59, the semicolon, which cannot appear in a version text. The split is at the first code 59; a second one lands in the second text and makes it rejected. The answer is `lt`, `eq`, or `gt`, or `none` when either text is rejected. A `cmp` request with no code 59 in it is malformed.

A malformed request prints `error`: an unknown operation, numbers that are not plain decimal digits, a code that is not a Unicode scalar value, more than one space in the line, or the `cmp` case above. A line may end in LF or CR LF; nothing else around a request is ignored.
