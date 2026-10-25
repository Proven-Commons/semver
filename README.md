# semver

A Semantic Versioning 2.0.0 parser, printer, and precedence comparison in Lean, with the round trip proved: parsing the printed form of a well formed version gives the version back.

The specification this follows is Semantic Versioning 2.0.0 at semver.org. `SPEC.md` states its rules as this library applies them.

## What it does

`Semver/Version.lean` holds the value type, the well-formedness rules, the printer, and the comparison. A version is three numbers, a list of prerelease identifiers, and a list of build identifiers held as text. A prerelease identifier is a number or a text. `Semver/Parse.lean` holds the parser. `Main.lean` is a small command-line front end the tests drive.

## What is proved

The definitions are in `Semver/Version.lean` and `Semver/Parse.lean`. The proofs are in `Proofs/`.

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed version gives the version back. | `Semver.Proofs.parse_print` |
| A version compares equal to itself. | `Semver.Proofs.compare_self` |
| Two versions that agree on the numbers and the prerelease compare equal, whatever their build metadata. | `Semver.Proofs.compare_eq_of_fields` |
| Changing only the build metadata leaves a version comparing equal to the original. | `Semver.Proofs.compare_build_irrel` |
| Each step of the section 11 example chain: 1.0.0-alpha < 1.0.0-alpha.1 < 1.0.0-alpha.beta < 1.0.0-beta < 1.0.0-beta.2 < 1.0.0-beta.11 < 1.0.0-rc.1 < 1.0.0. | `Semver.Examples.chain_1` to `chain_7` |

A version is well formed when each alphanumeric prerelease identifier is nonempty, holds only digits, ASCII letters, and hyphens, and holds at least one character that is not a digit, and each build identifier is nonempty and holds only those characters. The last rule for alphanumeric identifiers is what the type needs: an all-digit text is a number in this library, never an alphanumeric identifier, so a printed identifier reads back as the same kind.

The proved theorems check against the standard axioms only (`propext`, `Classical.choice`, `Quot.sound`), which a reader can confirm with the prints in `Semver/Verify.lean`.

## What is not proved

- That the parser accepts every text the grammar allows, and rejects every text it forbids. The round trip does not need either, so neither is proved. The test harness checks that behaviour against a Python oracle written from the specification text, and the results file records the outcome, including any failure.
- That `compare` is a full order. Reflexivity of equality under `compare` is proved, and build metadata is proved irrelevant. Transitivity and totality are not proved, so no claim is made that any two versions compare consistently across a chain of comparisons, beyond the proved example chain.
- Anything about version ranges, sorting lists of versions, or picking a version.
- Reading requests and printing answers in `Main.lean`: splitting lines, the decimal parser, the semicolon split, and the check that a code is a Unicode scalar value. The tests cover them, malformed requests included.
- Speed. The code works on lists of characters, which suits proofs, not large data.

## What you must trust

- The Lean kernel, which checks the proofs.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about.
- The operating system and hardware it runs on.
- The Python oracle in the test harness, written from the specification text, and the reader's own reading of Semantic Versioning 2.0.0, which the oracle and this code both follow.

This project has no dependencies beyond Lean itself.

## Run it

Needs Linux and [elan](https://github.com/leanprover/elan). Build, then feed request lines to the tool:

```
lake build
echo "parse 49,46,50,46,51" | .lake/build/bin/semver
```

That request is the text `1.2.3` as character codes, and the answer is `ok:49,46,50,46,51`. A text the parser rejects, such as the codes for `01.2.3`, answers `none`. A comparison request puts code 59 between the two texts and answers `lt`, `eq`, or `gt`. A malformed request answers `error`. See `SPEC.md` for the full protocol.

## Re-check it

```
lake build
python3 tests/run_tests.py
```

The test script rebuilds, reruns the fixed specification cases and the differential run against the oracle, and rewrites `tests/TEST-RESULTS.md`.
