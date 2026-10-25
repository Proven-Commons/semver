# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: a Python oracle written from the specification text in `tests/run_tests.py` (Python 3.12.3)
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261025

- fixed parse cases: 31 inputs, 31 agreements
- fixed cmp cases: 19 inputs, 19 agreements
- random valid versions, parse: 3000 inputs, 3000 agreements
- random version pairs, cmp: 3000 inputs, 3000 agreements
- mutated texts, parse: 3000 inputs, 3000 agreements
- soup texts, parse: 1500 inputs, 1500 agreements
- malformed requests: 12 inputs, 12 agreements
- Total: 10562 inputs, 10562 agreements
- Failures: 0
