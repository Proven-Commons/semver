# Specification: semver

This library reads and writes version strings in the form Semantic Versioning 2.0.0 sets out (https://semver.org/spec/v2.0.0.html), such as `1.0.0-beta.11+exp.sha.5114f85`. It also gives the precedence of two versions, as section 11 of that specification defines it. A reviewer who did not write this specification approves it. The approval also covers `SemVer/Spec.lean`, `SemVer/Spec/Defs.lean`, `SemVer/Types.lean`, and the other files `bar.toml` lists.

## The format

The scope is the `<valid semver>` rule of the Backus–Naur form grammar on semver.org:

```
<valid semver> ::= <version core>
                 | <version core> "-" <pre-release>
                 | <version core> "+" <build>
                 | <version core> "-" <pre-release> "+" <build>
<version core> ::= <major> "." <minor> "." <patch>
```

`SemVer/Spec/Defs.lean` writes out each rule of the grammar. In plain words:

- The major, minor and patch numbers are numeric identifiers: `0`, or ASCII digits that do not start with `0` (section 2). There is no upper limit on their size.
- The pre-release part follows a `-`. It is one or more identifiers joined by `.`. Each is a numeric identifier, which has no leading zero, or an alphanumeric identifier. An alphanumeric identifier is ASCII letters, digits and hyphens, with at least one letter or hyphen. So `0a` and `--` are identifiers, and `01` is not (section 9).
- The build part follows a `+`. It is one or more identifiers joined by `.`. Each is one or more ASCII letters, digits and hyphens, and may start with `0` (section 10).
- No identifier is empty.
- The parser reads nothing else. That includes:
  - a `v` or `=` before the version;
  - spaces or a line break before or after it;
  - a version with fewer or more than three numbers;
  - digits and letters outside ASCII, such as `١` and `１`;
  - the ranges and shorthands that package managers accept, such as `^1.2` or `1.x`.

## The value

`parse` returns a `Version`: the three numbers, the list of pre-release identifiers, and the list of build identifiers. Each pre-release identifier is a number (`num`) when it is all digits, and its text (`alnum`) otherwise. Each build identifier is its text. A list is empty when its part is absent. `SemVer.Spec.Valid` says which values are well formed: every `alnum` identifier is an alphanumeric identifier, and every build identifier is one or more identifier characters.

`Version.print` writes a version: the three numbers in decimal, then `-` and the pre-release identifiers, then `+` and the build identifiers. Each list is joined by `.` and left out, with its sign, when it is empty.

## Precedence

`Version.compare` gives the precedence of `a` against `b`: `.lt` when `a` has lower precedence, `.eq` when the two have the same precedence, and `.gt` otherwise. It follows section 11:

1. Build identifiers play no part.
2. Major, minor and patch are compared as numbers, in that order. The first difference decides.
3. With the same three numbers, a version with a pre-release part comes before one without.
4. Two pre-release parts are compared identifier by identifier, from the left, until one differs:
   1. Two numbers are compared as numbers.
   2. Two other identifiers are compared in ASCII order, character by character. When one runs out first, it comes first.
   3. A number comes before any other identifier.
   4. When one list runs out first, all its identifiers being equal to the other's, it comes first.

So two versions have the same precedence exactly when they differ in build identifiers at most. `SemVer.Spec.precedence` in `SemVer/Spec/Defs.lean` states these rules as written.

## Errors

`parse` returns `none` for any string it does not accept. No function can fail any other way.

## The command-line tool

The command-line tool in `Main.lean` has two modes:

- `semver check VERSION...` prints each version's printed form, or `invalid`. It exits with 1 when any version is invalid.
- `semver serve` answers requests from the differential tests, one per line. Each string is sent as the hex digits of its UTF-8 bytes. The header comment of `Main.lean` gives the protocol.

Every answer comes from `parse`, `Version.print` and `Version.compare`.

## What must always hold

Each property is a theorem in `SemVer/Spec.lean`, under the name given. The definitions the statements use are in `SemVer/Spec/Defs.lean`. They are written from the specification and checked against its examples.

| Property | Theorem |
|----------|---------|
| `print` writes a version as `SemVer.Spec.render` sets out. | `SemVer.Spec.print_eq` |
| `parse` returns `v` exactly when `v` is well formed and the string is how `v` is written. | `SemVer.Spec.parse_iff` |
| `parse` accepts exactly the strings of the grammar on semver.org. | `SemVer.Spec.parse_isSome_iff` |
| What `parse` returns is well formed. | `SemVer.Spec.parse_valid` |
| Printing then parsing gives a well formed version back. | `SemVer.Spec.parse_print` |
| Parsing then printing gives the string back. | `SemVer.Spec.print_parse` |
| `compare` gives the precedence of section 11, as `SemVer.Spec.precedence` states it. | `SemVer.Spec.compare_eq` |
| Changing the build identifiers of either version changes no answer of `compare`. | `SemVer.Spec.compare_build` |
| `compare` gives `.eq` exactly when the numbers and the pre-release identifiers are the same. | `SemVer.Spec.compare_eq_eq_iff` |
| Swapping the two versions swaps the answer. | `SemVer.Spec.compare_swap` |
| Precedence is transitive, both "at most" and "lower". | `SemVer.Spec.compare_trans`, `SemVer.Spec.compare_lt_trans` |
| The examples of sections 9 and 10 parse to the parts the specification reads them as. | `SemVer.Spec.semver_examples` |
| The example lists of section 11 are in rising order, every version below every later one. Two versions that differ only in build metadata have the same precedence. | `SemVer.Spec.precedence_examples` |
| Leading zeros, missing and extra parts, empty identifiers, characters outside the grammar, and text around the version are rejected. | `SemVer.Spec.reject_vectors` |
| Leading zeros in alphanumeric and build identifiers, an identifier of hyphens, and numbers past 64 bits are accepted. | `SemVer.Spec.accept_vectors` |

Together, these fix every output.

- `parse` is fixed for every string by `SemVer.Spec.parse_iff`.
- `print` is fixed for every version by `SemVer.Spec.print_eq`.
- `compare` is fixed for every pair of versions by `SemVer.Spec.compare_eq`.
- A parser that accepted nothing would meet `SemVer.Spec.parse_valid`, but it would fail `SemVer.Spec.parse_iff`, `SemVer.Spec.parse_isSome_iff` and `SemVer.Spec.parse_print`.
- A parser that accepted too much would fail `SemVer.Spec.parse_iff` and `SemVer.Spec.parse_isSome_iff`.

## Oracle

The differential tests compare the tool with python-semver 3.1.0, `semver.Version.parse` and `Version.compare`. Every string python-semver accepts must also match, in full, the regular expression semver.org gives in its FAQ, and every string it rejects must not.
