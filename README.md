# semver: Semantic Versioning, proved

This library reads and writes Semantic Versioning 2.0.0 strings in Lean, and gives the precedence of two versions. Machine-checked proofs show four things:

- The parser accepts exactly the strings of the grammar on semver.org, and nothing else.
- It returns each part as written, and printing what it returns gives the string back.
- `compare` follows the precedence rules of section 11, as `SemVer/Spec/Defs.lean` states them.
- That order is consistent: swapping the sides swaps the answer, it is transitive, and two versions tie exactly when they differ in build metadata at most.

So `01.0.0`, `1.0.0-01`, `v1.0.0`, `1.0` and `1.0.0 ` are rejected, `1.0.0-0a` and `1.0.0+001` are accepted, and numbers have no upper limit.

It is tested against python-semver, with the regular expression semver.org gives as a second check; `tests/TEST-RESULTS.md` has the record. It is a project of [Proven Commons](https://github.com/Proven-Commons/mission), built to the verified bar published there.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, so this is not verified.

## Use it

From Lean:

- `SemVer.parse : String → Option SemVer.Version`
- `SemVer.Version.print : SemVer.Version → String`
- `SemVer.Version.compare : SemVer.Version → SemVer.Version → Ordering`

`SPEC.md` says what each one does.

## What is proved

The statements are in `SemVer/Spec.lean`, the definitions they use in `SemVer/Spec/Defs.lean`, and the proofs in `SemVer/Proofs/`.

| Claim | Theorem |
|-------|---------|
| `print` writes the three numbers in decimal, then the pre-release and build identifiers, each part left out when it is empty. | `SemVer.Spec.print_eq` |
| `parse` returns a version exactly when the version is well formed and the string is how it is written. So it returns the parts as written, and there is one way to write each version. | `SemVer.Spec.parse_iff` |
| `parse` accepts exactly the strings of the grammar on semver.org, as `SemVer/Spec/Defs.lean` writes it out. It rejects leading zeros in numbers and in numeric pre-release identifiers, empty identifiers, characters other than ASCII letters, digits and hyphens, and anything before or after the version. | `SemVer.Spec.parse_isSome_iff` |
| What `parse` returns is well formed. | `SemVer.Spec.parse_valid` |
| Printing a well formed version and parsing the result gives it back. | `SemVer.Spec.parse_print` |
| Parsing a string and printing the result gives the string back. | `SemVer.Spec.print_parse` |
| `compare` follows section 11: major, minor and patch as numbers, then a version with a pre-release part below one without, then the pre-release identifiers from the left, numbers as numbers and below other identifiers, other identifiers in ASCII order, and a shorter list first when it runs out. | `SemVer.Spec.compare_eq` |
| Build metadata plays no part: changing it on either side changes no answer. | `SemVer.Spec.compare_build` |
| Two versions have the same precedence exactly when they differ in build metadata at most. | `SemVer.Spec.compare_eq_eq_iff` |
| Swapping the two versions swaps the answer, and precedence is transitive. So sorting by it is consistent. | `SemVer.Spec.compare_swap`, `SemVer.Spec.compare_trans`, `SemVer.Spec.compare_lt_trans` |
| The examples of sections 9 to 11, both ways; a selection of strings outside the grammar; and strings inside it that loose parsers get wrong. | `SemVer.Spec.semver_examples`, `SemVer.Spec.precedence_examples`, `SemVer.Spec.reject_vectors`, `SemVer.Spec.accept_vectors` |

The command-line tool in `Main.lean` answers `parse` and `compare` requests with these functions directly.

## What is not proved

- Reading requests and printing answers in `Main.lean`: the hex parsing and printing, and the request format. The differential tests cover them, with malformed requests and CR LF line endings.
- Whether a project followed the rules of sections 1 to 8, on when to change which number. Those rules are about people's choices, not strings.
- Anything outside section 11's precedence. Build metadata has no order here, though some libraries order it to break ties. There are no version ranges, such as `^1.2.3` or `>=1.0.0 <2.0.0`, and no loose forms, such as `v1.2.3` or `1.2`.
- Speed and size. The code works on lists and recurses once per character, which suits proofs, not bulk data. With an 8 MB stack, a string of 4 million characters is answered, but one of 16 million runs out of stack. The program then stops, with the answers before it already written, and never gives a wrong answer. Reading and printing a number takes time that grows with the square of its length: a number of 100,000 digits takes seconds.
- Numbers with more than 4,300 digits are outside the tests. Python refuses to read them by default, so the oracle cannot answer.

## What you must trust

- The Lean kernel and the five external kernels shipped with Lean, which all check the proofs.
- `lake comparator`, which builds the statements and the proofs in a sandbox, exports them, and checks that each proof proves exactly its statement.
- bubblewrap and the Linux kernel's namespaces, which keep the untrusted build from tampering with that check.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about (by `implemented_by` and `extern`), such as the arithmetic on natural numbers, `Nat.repr`, which `print` uses to write numbers, and the conversion between strings and lists.
- The operating system and hardware it runs on.
- python-semver 3.1.0, as the oracle in the differential tests. The record names its version.

This project has no dependencies beyond Lean itself.

## Re-check it

Needs Linux, [elan](https://github.com/leanprover/elan), bubblewrap (`apt install bubblewrap`), and Python 3.

```
lake build
lake comparator --paranoid
python3 tests/run_tests.py
python3 tests/plant_bugs.py
```

`lake comparator --paranoid` builds the statements and the proofs in a sandbox. It checks that each theorem in `SemVer/Proofs/` proves exactly the statement in `SemVer/Spec.lean`, using only the axioms `propext`, `Classical.choice`, and `Quot.sound`, and replays it through every kernel shipped with Lean.

The test script compares the tool with python-semver. It runs every string of up to eight characters over `0`, `1`, `.`, `-`, `+` and `a`, the examples of the specification, and random and mutated versions from a recorded seed, then compares pairs of versions. It then rewrites `tests/TEST-RESULTS.md`. When Python lacks python-semver 3.1.0, it installs it into `.lake/oracle-venv`, checked against the hashes in `tests/oracle-requirements.txt`.

`tests/plant_bugs.py` plants ten bugs in a copy of the code, one at a time, and records in `tests/PLANTED-BUGS.md` how many failures the tests report for each. Every bug must be caught, and each of them also breaks a proof.

## Layout

- `SemVer/Types.lean`: the `Version` and `Ident` types.
- `SemVer/Basic.lean`: the code under proof.
- `SemVer/Spec.lean`: the statements, with `sorry` for proofs. A reviewer approves this file.
- `SemVer/Spec/Defs.lean`: the definitions the statements use, written from the grammar and section 11, with checks against the specification's examples.
- `SemVer/Proofs.lean` and `SemVer/Proofs/`: the proofs, under the same names.
- `Main.lean`: the command-line tool the tests drive.
- `lakefile.toml`: the build. It names the package and its version, its libraries and executable, and the default targets, and sets nothing else.
- `comparator.json`: which theorems `lake comparator` checks, and which axioms it allows.
- `bar.toml`: the record for the bar check: status, authors, approvals, and where things are.
- `SPEC.md`: the specification in plain words.
- `tests/run_tests.py`: the differential tests.
- `tests/oracle-requirements.txt`: the oracle's version, pinned by hash.
- `tests/plant_bugs.py` and `tests/PLANTED-BUGS.md`: the planted bugs, and the record that the tests catch each one.
