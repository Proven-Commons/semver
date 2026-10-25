#!/usr/bin/env python3
"""Tests for the Lean SemVer parser, printer, and precedence.

Three parts.

1. Fixed cases. The precedence chain from section 11 of the
   specification as `cmp` requests, the valid example texts from
   the specification as `parse` requests (each must answer with
   its own text back, since each is already canonical), and
   texts the grammar forbids (each must be rejected).

2. A differential run against a Python oracle written from the
   specification text with plain string code. Python's standard
   library has no semver module, and `packaging` is not semver,
   so neither is used. Random valid versions are built from
   parts; random pairs are compared; random text mutations and
   random soup texts must be read alike by both sides, as a
   canonical print or as a rejection.

3. Malformed request lines must be answered `error`.

The oracle and the generator share no code with the Lean side.
The seed is recorded in the results file.

    python3 tests/run_tests.py [--seed N] [--count N]

The tool is driven one batch process per chunk of requests:
input written and closed, output drained until the process
exits. The harness builds the executable first, writes
tests/TEST-RESULTS.md, and exits non-zero if any check fails.
It needs Python 3.11 or later.
"""

import argparse
import random
import subprocess
import sys
import threading
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "semver"
RESULTS = ROOT / "tests" / "TEST-RESULTS.md"
TIMEOUT = 900
BUILD_TIMEOUT = 3600
CHUNK = 2000

SEED_DEFAULT = 20261025

DIGITS = "0123456789"
IDCHARS = set(DIGITS + "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz-")


def codes(text):
    return ",".join(str(ord(c)) for c in text)


def parse_request(text):
    return "parse " + codes(text)


def cmp_request(a, b):
    return "cmp " + codes(a) + ",59," + codes(b)


def run_tool(lines, timeout=TIMEOUT):
    """Run the tool on a batch of request lines.

    Returns (answers, problem). No right answer is longer than
    its request plus a small constant, so output past twice the
    input plus 64 bytes a line is stopped, not read until memory
    runs out.
    """
    data = "".join(line + "\n" for line in lines)
    raw = data.encode("utf-8")
    limit = 2 * len(raw) + 64 * (len(lines) + 1)
    try:
        proc = subprocess.Popen(
            [str(EXE)],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except OSError as e:
        return [], f"could not run {EXE}: {e.strerror or e}"
    out, err = bytearray(), bytearray()

    def feed():
        try:
            proc.stdin.write(raw)
            proc.stdin.close()
        except (BrokenPipeError, ValueError):
            pass

    def drain(stream, buf, cap):
        while chunk := stream.read1(1 << 16):
            buf += chunk
            if len(buf) > cap:
                proc.kill()
                return

    threads = [
        threading.Thread(target=feed),
        threading.Thread(target=drain, args=(proc.stdout, out, limit)),
        threading.Thread(target=drain, args=(proc.stderr, err, 1 << 20)),
    ]
    for t in threads:
        t.start()
    problem = None
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        problem = f"no end after {timeout} seconds"
    for t in threads:
        t.join()
    proc.wait()
    if len(out) > limit:
        problem = problem or f"more than {limit} bytes of output, stopped"
    elif proc.returncode != 0 and not problem:
        tail = " / ".join(
            bytes(err).decode("utf-8", "backslashreplace").splitlines()[-3:]
        )
        problem = f"exit status {proc.returncode}: {tail}"
    text = bytes(out).decode("utf-8", "backslashreplace")
    if text and not text.endswith("\n"):
        problem = problem or "the last answer has no LF"
    answers = text.split("\n")
    if answers and answers[-1] == "":
        answers.pop()
    if len(answers) != len(lines) and not problem:
        problem = f"{len(lines)} requests but {len(answers)} answers"
    return answers, problem


# ------------------------------------------------------------------
# The oracle, written from the specification text.
#
# A parsed version is (numbers, prerelease identifiers, build
# identifiers): numbers is a list of three ints; a prerelease
# identifier is ("n", int) or ("a", text); build identifiers are
# text. Parsing returns None for a text the grammar forbids.


def is_digits(s):
    return s != "" and all(c in DIGITS for c in s)


def num_ok(s):
    return is_digits(s) and (s == "0" or not s.startswith("0"))


def id_ok(s):
    return s != "" and all(c in IDCHARS for c in s)


def oracle_parse(text):
    if text == "":
        return None
    if "+" in text:
        core_pre, build = text.split("+", 1)
    else:
        core_pre, build = text, None
    if "-" in core_pre:
        core, pre = core_pre.split("-", 1)
    else:
        core, pre = core_pre, None
    parts = core.split(".")
    if len(parts) != 3 or not all(num_ok(p) for p in parts):
        return None
    numbers = [int(p) for p in parts]
    pre_ids = []
    if pre is not None:
        for ident in pre.split("."):
            if not id_ok(ident):
                return None
            if is_digits(ident):
                if not num_ok(ident):
                    return None
                pre_ids.append(("n", int(ident)))
            else:
                pre_ids.append(("a", ident))
    build_ids = []
    if build is not None:
        for ident in build.split("."):
            if not id_ok(ident):
                return None
            build_ids.append(ident)
    return numbers, pre_ids, build_ids


def oracle_print(parsed):
    numbers, pre_ids, build_ids = parsed
    out = ".".join(str(n) for n in numbers)
    if pre_ids:
        out += "-" + ".".join(
            str(v) if kind == "n" else v for kind, v in pre_ids
        )
    if build_ids:
        out += "+" + ".".join(build_ids)
    return out


def expected_parse_answer(text):
    parsed = oracle_parse(text)
    if parsed is None:
        return "none"
    return "ok:" + codes(oracle_print(parsed))


def cmp_id(x, y):
    if x[0] == "n" and y[0] == "n":
        if x[1] == y[1]:
            return "eq"
        return "lt" if x[1] < y[1] else "gt"
    if x[0] == "n":
        return "lt"
    if y[0] == "n":
        return "gt"
    if x[1] == y[1]:
        return "eq"
    return "lt" if x[1] < y[1] else "gt"


def oracle_cmp(a_text, b_text):
    pa = oracle_parse(a_text)
    pb = oracle_parse(b_text)
    if pa is None or pb is None:
        return "none"
    if pa[0] != pb[0]:
        return "lt" if pa[0] < pb[0] else "gt"
    a, b = pa[1], pb[1]
    if not a and not b:
        return "eq"
    if not a:
        return "gt"
    if not b:
        return "lt"
    for x, y in zip(a, b):
        c = cmp_id(x, y)
        if c != "eq":
            return c
    if len(a) == len(b):
        return "eq"
    return "lt" if len(a) < len(b) else "gt"


# ------------------------------------------------------------------
# Fixed cases.

CHAIN = [
    "1.0.0-alpha",
    "1.0.0-alpha.1",
    "1.0.0-alpha.beta",
    "1.0.0-beta",
    "1.0.0-beta.2",
    "1.0.0-beta.11",
    "1.0.0-rc.1",
    "1.0.0",
]

VALID = [
    "1.0.0-alpha",
    "1.0.0-alpha.1",
    "1.0.0-0.3.7",
    "1.0.0-x-y-z.-",
    "1.0.0-alpha+001",
    "1.0.0+20130313144700",
    "1.0.0-beta+exp.sha.5114f85",
    "1.0.0",
    "0.0.0",
    "999999.8888.7777-rc.99+build.01",
]

INVALID = [
    "01.2.3",
    "1.02.3",
    "1.0.0-01",
    "1.0.0-alpha..1",
    "1.0.0-+",
    "1.0.0+",
    "1.0.0-",
    "1.0",
    "1.0.0.0",
    "v1.2.3",
    "1.0.0-alpha_beta",
    "",
    "1..2",
    "1.0.0-alpha.01",
    "1.0.0++1",
    "-1.0.0",
    "1.0.0 ",
    " 1.0.0",
    "1.0.0-rc.1+build+more",
]

MALFORMED = [
    " ",
    "parse 1,,2",
    "parse 12a",
    "cmp",
    "cmp 49,50",
    "cmp ;",
    "bogus 1,2",
    "parse 55296",
    "parse 1114112",
    "parse 49 50",
    " parse 49",
    "parse 49,",
]


def random_version(rng):
    def core_num():
        return rng.choice([0, 1, 2, 9, 10, 42, 999, rng.randrange(0, 10**9)])

    def pre_id():
        if rng.random() < 0.5:
            return ("n", rng.choice([0, 1, 7, 11, 99, rng.randrange(0, 10**6)]))
        n = rng.randrange(1, 7)
        chars = []
        for _ in range(n):
            chars.append(rng.choice("abcdefghijklmnopqrstuvwxyzABCZ0123456789-"))
        text = "".join(chars)
        if all(c in DIGITS for c in text):
            text += rng.choice("aZ-")
        return ("a", text)

    def build_id():
        n = rng.randrange(1, 7)
        return "".join(rng.choice("0123456789abcXYZ-") for _ in range(n))

    numbers = [core_num(), core_num(), core_num()]
    pre_ids = [pre_id() for _ in range(rng.randrange(0, 4))]
    build_ids = [build_id() for _ in range(rng.randrange(0, 3))]
    return numbers, pre_ids, build_ids


def mutate(rng, text):
    chars = list(text)
    alphabet = "0123456789aZ-.+_;vx "
    for _ in range(rng.randrange(1, 4)):
        if not chars:
            break
        op = rng.choice(["replace", "insert", "delete", "swap"])
        i = rng.randrange(0, len(chars))
        if op == "replace":
            chars[i] = rng.choice(alphabet)
        elif op == "insert":
            chars.insert(i, rng.choice(alphabet))
        elif op == "delete":
            del chars[i]
        elif i + 1 < len(chars):
            chars[i], chars[i + 1] = chars[i + 1], chars[i]
    return "".join(chars)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=SEED_DEFAULT)
    ap.add_argument("--count", type=int, default=3000)
    args = ap.parse_args()
    rng = random.Random(args.seed)

    print("building...", flush=True)
    build = subprocess.run(
        ["lake", "build"], cwd=ROOT, capture_output=True, text=True,
        timeout=BUILD_TIMEOUT,
    )
    if build.returncode != 0:
        print(build.stdout[-3000:])
        print(build.stderr[-3000:])
        return 1

    sections = []  # (name, requests, expected)
    failures = []
    problems = []

    def section(name, pairs):
        sections.append((name, [r for r, _ in pairs], [e for _, e in pairs]))

    fixed_parse = [(parse_request(t), expected_parse_answer(t)) for t in VALID + INVALID]
    fixed_parse.append(("parse", "none"))
    fixed_parse.append(("parse ", "none"))
    section("fixed parse cases", fixed_parse)

    fixed_cmp = []
    for a, b in zip(CHAIN, CHAIN[1:]):
        fixed_cmp.append((cmp_request(a, b), "lt"))
        fixed_cmp.append((cmp_request(b, a), "gt"))
    fixed_cmp.append((cmp_request(CHAIN[0], CHAIN[-1]), "lt"))
    fixed_cmp.append((cmp_request("1.0.0+build.1", "1.0.0+other.2"), "eq"))
    fixed_cmp.append((cmp_request("2.1.1", "2.1.0"), "gt"))
    fixed_cmp.append((cmp_request("1.0", "1.0.0"), "none"))
    fixed_cmp.append(("cmp 49,59", "none"))
    section("fixed cmp cases", fixed_cmp)

    rand_parse = []
    texts = []
    for _ in range(args.count):
        v = random_version(rng)
        text = oracle_print(v)
        texts.append(text)
        rand_parse.append((parse_request(text), "ok:" + codes(text)))
    section("random valid versions, parse", rand_parse)

    rand_cmp = []
    for _ in range(args.count):
        a = oracle_print(random_version(rng))
        b = oracle_print(random_version(rng))
        rand_cmp.append((cmp_request(a, b), oracle_cmp(a, b)))
    section("random version pairs, cmp", rand_cmp)

    mutated = []
    for text in texts:
        m = mutate(rng, text)
        mutated.append((parse_request(m), expected_parse_answer(m)))
    section("mutated texts, parse", mutated)

    soup = []
    soup_alphabet = "01.-+aZ; "
    for _ in range(args.count // 2):
        n = rng.randrange(0, 15)
        text = "".join(rng.choice(soup_alphabet) for _ in range(n))
        soup.append((parse_request(text), expected_parse_answer(text)))
    section("soup texts, parse", soup)

    section("malformed requests", [(line, "error") for line in MALFORMED])

    lines_out = []
    lines_out.append("# Test results")
    lines_out.append("")
    lines_out.append(
        "Written by `tests/run_tests.py`. Rerun it to check these numbers."
    )
    lines_out.append("")
    import platform

    lean_version = subprocess.run(
        ["lake", "env", "lean", "--version"], cwd=ROOT,
        capture_output=True, text=True,
    ).stdout.strip()
    lines_out.append(f"- Oracle: a Python oracle written from the specification text in `tests/run_tests.py` (Python {platform.python_version()})")
    lines_out.append(f"- Lean: {lean_version}")
    lines_out.append(f"- Seed: {args.seed}")
    lines_out.append("")

    total_inputs = 0
    total_agree = 0
    for name, requests, expected in sections:
        answers = []
        for i in range(0, len(requests), CHUNK):
            chunk_answers, problem = run_tool(requests[i:i + CHUNK])
            if problem:
                problems.append(f"{name}: {problem}")
                chunk_answers = ["<no answer>"] * (len(requests[i:i + CHUNK]))
            answers.extend(chunk_answers)
        agree = 0
        for req, exp, ans in zip(requests, expected, answers):
            total_inputs += 1
            if ans == exp:
                agree += 1
                total_agree += 1
            elif len(failures) < 25:
                failures.append(f"{name}: request {req!r}: expected {exp!r}, got {ans!r}")
        lines_out.append(f"- {name}: {len(requests)} inputs, {agree} agreements")
    lines_out.append(f"- Total: {total_inputs} inputs, {total_agree} agreements")
    fail_count = total_inputs - total_agree
    lines_out.append(f"- Failures: {fail_count}")
    if problems:
        lines_out.append(f"- Tool problems: {len(problems)}")
    if failures or problems:
        lines_out.append("")
        lines_out.append("## Failures and problems")
        lines_out.append("")
        for f in (problems + failures)[:25]:
            lines_out.append(f"- {f}")
    lines_out.append("")
    RESULTS.write_text("\n".join(lines_out), encoding="utf-8")
    print("\n".join(lines_out))
    return 0 if fail_count == 0 and not problems else 1


if __name__ == "__main__":
    sys.exit(main())
