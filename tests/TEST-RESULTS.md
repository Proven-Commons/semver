# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: python-semver 3.1.0 on Python 3.13.17, with the semver.org FAQ regular expression as a second check on acceptance
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261025
- Inputs: 3021721
- Mutated: 449861 of the inputs are mutated versions
- By kind: compare 150022, compare pool 6084, error 13, examples 85, grid 2015539, mutated 449861, random 100539, valid 299578
- Strings parsed: 2865602, of which 442325 accepted and 2423277 rejected
- Accepted versions with a number of 2**64 or more: 72009
- Pairs compared: 156106: < 66963, = 27956, > 61187, REJECT 0
- Malformed requests answered `error`: 13 of 13
- Requests ending in CR LF: every seventh, 431674
- Last lines sent alone, with no LF or with CR LF, answered right: 3 of 3
- Failures: 0
