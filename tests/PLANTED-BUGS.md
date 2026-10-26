# Planted bugs

Written by `tests/plant_bugs.py`. Each bug is a one-line change to `SemVer/Basic.lean`, tested with `tests/run_tests.py --count 2000`. Every bug must give failures, and the unchanged code none.

| Planted bug | Failures |
|---|---|
| none | 0 |
| leading zeros are accepted in numbers | 874 |
| identifiers are compared by length only, not in ASCII order | 338 |
| a hyphen is not an identifier character | 945 |
| an empty build identifier is accepted | 257 |
| a numeric identifier comes after an alphanumeric one | 309 |
| a version with a pre-release part comes after the release | 163 |
| pre-release identifiers are compared the wrong way round | 1471 |
| build metadata takes part in precedence | 47 |
| numeric identifiers are compared as text | 17 |
| a hyphen in the build part starts the pre-release part | 1418 |

Bugs caught: 10 of 10
