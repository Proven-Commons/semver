#!/usr/bin/env python3
"""Differential tests: the Lean SemVer parser and precedence against
python-semver.

The oracle is python-semver 3.1.0 (https://pypi.org/project/semver/):
`semver.Version.parse`, which raises on any string outside the
SemVer 2.0.0 grammar, and `Version.compare`, which gives section 11
precedence. Every accepted string must also match, in full, the
regular expression semver.org gives in its FAQ, compiled with
`re.ASCII`; a string where the two oracles disagree is a failure too.

For `parse`, the expected answer is python-semver's version: its
printed form, its three numbers, its pre-release identifiers, each
tagged as a number (digits only) or not, and its build identifiers.
For `compare`, it is python-semver's answer, or REJECT when either
string is not a version.

Inputs come from a recorded seed, after fixed sets:

- every string of up to eight characters over `0`, `1`, `.`, `-`,
  `+` and `a`, which reaches every arrangement of parts and
  separators with short parts;
- the examples of sections 9 to 11 of the specification, and strings
  outside the grammar that loose parsers accept;
- random versions with numbers up to 2**200, pre-release identifiers
  that are numbers, letters, hyphens and mixtures (`0a`, `--`), and
  build identifiers with leading zeros;
- mutations of those: a character changed, dropped, added or
  doubled, a leading zero put in front of a number, the string cut
  short, a prefix such as `v` or a space or line break around it,
  and digits from other scripts put in;
- random short strings;
- comparisons: every pair from a pool of versions built to differ in
  one place at a time, and random pairs of random versions;
- malformed requests, which the tool must answer with `error`.

Every seventh request ends in CR LF.

When this Python lacks python-semver 3.1.0, the script creates a
virtual environment in `.lake/oracle-venv`, installs it there, checked
against the hashes in `tests/oracle-requirements.txt`, and runs itself
again with it.

    python3 tests/run_tests.py [--seed N] [--count N]

`--count` is the number of random inputs after the fixed sets. The
script builds the executable first, writes tests/TEST-RESULTS.md, and
exits non-zero if any input disagrees.
"""

import argparse
import itertools
import os
import platform
import random
import re
import subprocess
import sys
import threading
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "semver"
RESULTS = ROOT / "tests" / "TEST-RESULTS.md"
REQUIREMENTS = ROOT / "tests" / "oracle-requirements.txt"
VENV = ROOT / ".lake" / "oracle-venv"
PKGS = ROOT / ".lake" / "oracle-packages"
PIN = "3.1.0"
TIMEOUT = 1800
BUILD_TIMEOUT = 3600


def oracle_ready():
    """Whether the pinned python-semver imports."""
    try:
        import semver
    except ImportError:
        return False
    return semver.__version__ == PIN


def ensure_oracle():
    """Import the oracle. When this Python lacks the pinned version,
    install it, checked against the hashes in
    tests/oracle-requirements.txt, into a virtual environment and run
    again with it; where a virtual environment cannot be made, install
    it into a folder instead and import it from there."""
    if oracle_ready():
        return
    if os.environ.get("SEMVER_ORACLE_VENV"):
        sys.exit(f"python-semver {PIN} is not usable even in .lake/oracle-venv")
    pip = ["-m", "pip", "install", "--quiet", "--require-hashes", "-r", str(REQUIREMENTS)]
    python = VENV / "bin" / "python"
    made = python.exists() or subprocess.run(
        [sys.executable, "-m", "venv", str(VENV)], capture_output=True).returncode == 0
    if made:
        subprocess.run([str(python), *pip], check=True)
        env = dict(os.environ, SEMVER_ORACLE_VENV="1")
        os.execve(str(python), [str(python), *sys.argv], env)
    subprocess.run([sys.executable, *pip, "--break-system-packages", "--target", str(PKGS)],
                   check=True)
    sys.path.insert(0, str(PKGS))
    sys.modules.pop("semver", None)
    if not oracle_ready():
        sys.exit(f"python-semver {PIN} is not usable")


ensure_oracle()
import semver  # noqa: E402

# The regular expression of the semver.org FAQ, "Is there a suggested
# regular expression (RegEx) to check a SemVer string?", as written
# there. `re.ASCII` keeps `\d` to ASCII digits, and `fullmatch` keeps
# `$` from matching before a final line break.
SEMVER_ORG_REGEX = re.compile(
    r"^(0|[1-9]\d*)\.(0|[1-9]\d*)\.(0|[1-9]\d*)"
    r"(?:-((?:0|[1-9]\d*|\d*[a-zA-Z-][0-9a-zA-Z-]*)(?:\.(?:0|[1-9]\d*|\d*[a-zA-Z-][0-9a-zA-Z-]*))*))?"
    r"(?:\+([0-9a-zA-Z-]+(?:\.[0-9a-zA-Z-]+)*))?$",
    re.ASCII,
)


def oracle_version(s):
    """python-semver's reading of `s`, or None. Raises when the two
    oracles disagree."""
    try:
        v = semver.Version.parse(s)
    except (ValueError, TypeError):
        v = None
    if (v is not None) != (SEMVER_ORG_REGEX.fullmatch(s) is not None):
        raise OracleDisagree(s)
    return v


class OracleDisagree(Exception):
    pass


def ident_field(x):
    return f"n:{int(x)}" if x.isascii() and x.isdigit() else f"a:{x}"


def oracle_parse(s):
    v = oracle_version(s)
    if v is None:
        return "REJECT"
    pre = ",".join(ident_field(x) for x in v.prerelease.split(".")) if v.prerelease else ""
    build = ",".join(v.build.split(".")) if v.build else ""
    return "\t".join(["OK", str(v), str(v.major), str(v.minor), str(v.patch), pre, build])


def oracle_compare(a, b):
    va, vb = oracle_version(a), oracle_version(b)
    if va is None or vb is None:
        return "REJECT"
    return {-1: "<", 0: "=", 1: ">"}[va.compare(vb)]


# The fixed sets.

GRID_ALPHABET = "01.-+a"
GRID_LENGTH = 8


def grid():
    for n in range(GRID_LENGTH + 1):
        for t in itertools.product(GRID_ALPHABET, repeat=n):
            yield "".join(t)


EXAMPLES = [
    # Sections 9 and 10.
    "1.0.0-alpha", "1.0.0-alpha.1", "1.0.0-0.3.7", "1.0.0-x.7.z.92", "1.0.0-x-y-z.--",
    "1.0.0-alpha+001", "1.0.0+20130313144700", "1.0.0-beta+exp.sha.5114f85",
    "1.0.0+21AF26D3----117B344092BD",
    # Section 11.
    "1.0.0", "2.0.0", "2.1.0", "2.1.1", "1.0.0-alpha.beta", "1.0.0-beta", "1.0.0-beta.2",
    "1.0.0-beta.11", "1.0.0-rc.1",
    # Inside the grammar, often got wrong.
    "0.0.0", "0.0.0-0", "1.0.0-0a", "1.0.0-00a", "1.0.0--", "1.0.0---", "1.0.0-a-+b-",
    "1.0.0+001", "1.0.0+0", "1.0.0+-", "1.0.0-0.0.0", "1.0.0-alpha.0valid",
    "1.0.0-alpha-a.b-c-somethinglong+build.1-aef.1-its-okay", "1.0.0-rc.1+build.123",
    "10.20.30", "99999999999999999999999.999999999999999999.99999999999999999",
    "18446744073709551616.0.0", "1.2.3----RC-SNAPSHOT.12.9.1--.12+788",
    "1.2.3----R-S.12.9.1--.12+meta", "1.0.0-0A.is.legal", "2.0.0+build.1848",
    # Outside the grammar.
    "", "1", "1.2", "1.2.3.4", "01.1.1", "1.01.1", "1.1.01", "1.2.3-01", "1.2.3-0123",
    "1.2.3-0123.0123", "1.2.3-", "1.2.3+", "1.2.3-+", "1.2.3-+123", "1.2-SNAPSHOT",
    "1.2.31.2.3----RC-SNAPSHOT.12.09.1--..12+788", "-1.0.3-gamma+b7718", "+justmeta",
    "9.8.7+meta+meta", "9.8.7-whatever+meta+meta", "1.2.3.DEV", "1.2.3-alpha..1",
    "1.2.3-alpha.", "1.2.3+build..1", "1.2.3-alpha_beta", "1.2.3-alpha.é", "v1.2.3",
    "=1.2.3", " 1.2.3", "1.2.3 ", "1.2.3\n", "\n1.2.3", "1.2.3\t", "1٣.2.3",
    "1.2.3-١", "１.2.3", "1.2.3-a ", "1.2.3+٣", "1.2.3-K",
    "1.2.3-İ", "1.2.3\x00", "1..2.3", ".1.2.3", "1.2.3.", "a.b.c", "1.2.3-α",
]

ASCII_PRINTABLE = [chr(c) for c in range(32, 127)]
OTHER_CHARS = ["٣", "０", "１", "०", "é", "K", "İ",
               " ", "\t", "\n", "\r", "\x00", "‐", "−", "﹣", "．"]


def random_number(rng):
    r = rng.random()
    if r < 0.3:
        return rng.randint(0, 9)
    if r < 0.6:
        return rng.randint(10, 999)
    if r < 0.8:
        return rng.randint(1000, 2 ** 32)
    if r < 0.95:
        return rng.randint(2 ** 63 - 2, 2 ** 64 + 2)
    return rng.randint(0, 2 ** 200)


def random_ident_text(rng, alphabet, n):
    return "".join(rng.choice(alphabet) for _ in range(n))


ALNUM = "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ-"


def random_pre_ident(rng):
    r = rng.random()
    if r < 0.4:
        return str(random_number(rng))
    if r < 0.5:
        return rng.choice(["alpha", "beta", "rc", "pre", "SNAPSHOT", "-", "--", "0a", "a0"])
    while True:
        s = random_ident_text(rng, ALNUM, rng.randint(1, 8))
        if not s.isdigit():
            return s


def random_build_ident(rng):
    r = rng.random()
    if r < 0.3:
        return "".join(rng.choice("0123456789") for _ in range(rng.randint(1, 6)))
    return random_ident_text(rng, ALNUM, rng.randint(1, 8))


def random_version(rng):
    s = ".".join(str(random_number(rng)) for _ in range(3))
    if rng.random() < 0.6:
        s += "-" + ".".join(random_pre_ident(rng) for _ in range(rng.randint(1, 4)))
    if rng.random() < 0.4:
        s += "+" + ".".join(random_build_ident(rng) for _ in range(rng.randint(1, 3)))
    return s


def mutate(rng, s):
    cs = list(s)
    op = rng.randrange(10)
    if op == 0 and cs:
        cs[rng.randrange(len(cs))] = rng.choice(ASCII_PRINTABLE + list("0.-+"))
    elif op == 1 and cs:
        del cs[rng.randrange(len(cs))]
    elif op == 2:
        cs.insert(rng.randint(0, len(cs)), rng.choice(list("0123456789.-+aZ") + ASCII_PRINTABLE))
    elif op == 3 and cs:
        i = rng.randrange(len(cs))
        cs.insert(i, cs[i])
    elif op == 4:
        # A leading zero in front of a number or an identifier.
        starts = [i for i in range(len(cs)) if i == 0 or cs[i - 1] in ".-+"]
        cs.insert(rng.choice(starts) if starts else 0, "0")
    elif op == 5 and cs:
        cs = cs[: rng.randrange(len(cs))]
    elif op == 6:
        cs = list(rng.choice(["v", "V", "=", " ", "\n", "\t", "~", "^"])) + cs
    elif op == 7:
        cs += list(rng.choice([" ", "\n", "\r\n", "\t", ".", "-", "+", "\x00"]))
    elif op == 8 and cs:
        cs[rng.randrange(len(cs))] = rng.choice(OTHER_CHARS)
    else:
        cs.insert(rng.randint(0, len(cs)), rng.choice(OTHER_CHARS))
    return "".join(cs)


def compare_pool():
    """Versions built to differ from each other in one place at a time:
    each number, the presence of a pre-release part, each identifier's
    kind and value, the number of identifiers, and build metadata."""
    cores = ["0.0.0", "0.0.1", "0.1.0", "1.0.0", "1.0.1", "1.1.0", "2.0.0", "10.0.0",
             "1.10.0", "1.2.10", "18446744073709551616.0.0"]
    pres = ["", "-0", "-1", "-2", "-10", "-11", "-a", "-b", "-A", "-Z", "-z", "-0a", "-1a", "--",
            "-a-", "-alpha", "-alpha.1", "-alpha.beta", "-alpha.1.1", "-alpha.0", "-alpha.a",
            "-beta", "-beta.2", "-beta.11", "-rc.1", "-1.a", "-a.1", "-18446744073709551616"]
    builds = ["", "+b", "+001"]
    pool = []
    for c in ["1.0.0", "1.0.1"]:
        for p in pres:
            pool.append(c + p)
    for c in cores:
        pool.append(c)
        pool.append(c + "-alpha")
    for b in builds:
        pool.append("1.0.0-alpha" + b)
        pool.append("1.0.0" + b)
    return list(dict.fromkeys(pool))


def hexs(s):
    return s.encode("utf-8").hex()


MALFORMED = [
    ("frob 30", "unknown operation"),
    ("PARSE 30", "operations are lower case"),
    ("parse", "no argument"),
    ("parse 3", "an odd number of hex digits"),
    ("parse 3G", "not a hex digit"),
    ("parse 3A", "hex digits are lower case"),
    ("parse ff", "bytes that are not UTF-8"),
    ("parse 30 30", "two arguments"),
    ("compare 30", "one argument"),
    ("compare 30 30 30", "three arguments"),
    ("compare 3 30", "an odd number of hex digits"),
    ("", "an empty line"),
    (" parse 30", "a leading space"),
]

AT_EOF = [
    ("parse " + hexs("1.2.3"), oracle_parse("1.2.3")),
    ("compare " + hexs("1.0.0") + " " + hexs("2.0.0"), "<"),
    ("parse " + hexs("1.2.3") + "\r\n", oracle_parse("1.2.3")),
]


def parse_case(label, s, mutated=False):
    return (label, f"parse {hexs(s)}", oracle_parse(s), mutated)


def cases(seed, count):
    """(label, request, expected answer, mutated) for each input."""
    for req, _ in MALFORMED:
        yield ("error", req, "error", False)
    for s in EXAMPLES:
        yield parse_case("examples", s)
    for s in grid():
        yield parse_case("grid", s)
    pool = compare_pool()
    for a in pool:
        for b in pool:
            yield ("compare pool", f"compare {hexs(a)} {hexs(b)}", oracle_compare(a, b), False)
    rng = random.Random(seed)
    for _ in range(count):
        r = rng.random()
        if r < 0.3:
            yield parse_case("valid", random_version(rng))
        elif r < 0.75:
            base = random_version(rng)
            s = mutate(rng, base)
            while s == base:
                s = mutate(rng, base)
            yield parse_case("mutated", s, True)
        elif r < 0.85:
            n = rng.randint(0, 12)
            yield parse_case("random", "".join(rng.choice("0123456789.-+aZ" + "".join(OTHER_CHARS[:3]))
                                               for _ in range(n)))
        else:
            a = random_version(rng)
            b = random_version(rng) if rng.random() < 0.5 else mutate_compare(rng, a)
            yield ("compare", f"compare {hexs(a)} {hexs(b)}", oracle_compare(a, b), False)


def mutate_compare(rng, a):
    """A version near `a`: one identifier or number changed, or only the
    build metadata."""
    v = semver.Version.parse(a)
    op = rng.randrange(4)
    if op == 0:
        return str(v.replace(build=random_build_ident(rng)))
    if op == 1:
        return str(v.replace(patch=v.patch + rng.choice([0, 1])))
    if op == 2 and v.prerelease:
        parts = v.prerelease.split(".")
        parts[rng.randrange(len(parts))] = random_pre_ident(rng)
        return str(v.replace(prerelease=".".join(parts)))
    parts = v.prerelease.split(".") if v.prerelease else []
    parts.append(random_pre_ident(rng))
    return str(v.replace(prerelease=".".join(parts)))


def run_tool(data, timeout=TIMEOUT):
    """The tool's answer lines for `data`, and a note on how the run
    failed, or None."""
    raw = data.encode("utf-8")
    limit = 4 * len(raw) + 256 * (data.count("\n") + 1)
    try:
        proc = subprocess.Popen([str(EXE), "serve"], stdin=subprocess.PIPE,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    except OSError as e:
        return [], f"could not run {EXE.relative_to(ROOT)}: {e.strerror or e}"
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

    threads = [threading.Thread(target=feed),
               threading.Thread(target=drain, args=(proc.stdout, out, limit)),
               threading.Thread(target=drain, args=(proc.stderr, err, 1 << 20))]
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
        tail = " / ".join(err.decode("utf-8", "backslashreplace").splitlines()[-3:])
        problem = f"exit status {proc.returncode}: {tail}"
    text = bytes(out).decode("utf-8", "backslashreplace")
    if text and not text.endswith("\n"):
        problem = problem or "the last answer has no LF"
    lines = text.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    return lines, problem


def oracle():
    return (f"python-semver {semver.__version__} on Python {platform.python_version()}, "
            "with the semver.org FAQ regular expression as a second check on acceptance")


def lean_version():
    try:
        out = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT,
                             capture_output=True, text=True, errors="backslashreplace",
                             timeout=300)
        first = out.stdout.strip().splitlines()[:1]
        return first[0] if first else "unknown"
    except (OSError, subprocess.TimeoutExpired):
        return "unknown"


def count(text):
    n = int(text)
    if n < 1:
        raise argparse.ArgumentTypeError("the count must be at least 1")
    return n


def write(lines):
    RESULTS.write_text("\n".join(lines), encoding="utf-8")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20261025)
    ap.add_argument("--count", type=count, default=1_000_000)
    args = ap.parse_args()

    try:
        build = subprocess.run(["lake", "build", "semver"], cwd=ROOT, capture_output=True,
                               text=True, errors="backslashreplace", timeout=BUILD_TIMEOUT)
        built, log = build.returncode == 0, build.stdout + build.stderr
    except (OSError, subprocess.TimeoutExpired) as e:
        built, log = False, str(e)
    if not built:
        write(["# Test results", "", f"- Oracle: {oracle()}", f"- Seed: {args.seed}",
               "- Inputs: 0", "- Failures: 1 (`lake build semver` failed)", ""])
        sys.exit("lake build semver failed:\n" + log)

    try:
        items = list(cases(args.seed, args.count))
    except OracleDisagree as e:
        write(["# Test results", "", f"- Oracle: {oracle()}", f"- Seed: {args.seed}",
               "- Inputs: 0",
               f"- Failures: 1 (python-semver and the semver.org regex disagree on {e.args[0]!r})",
               ""])
        sys.exit(f"the two oracles disagree on {e.args[0]!r}")
    # Every seventh request ends in CR LF, which the tool must take as LF.
    out, problem = run_tool("".join(req + ("\r\n" if i % 7 == 6 else "\n")
                                    for i, (_, req, _, _) in enumerate(items)))
    failures = [("(whole run)", "a clean run", problem)] if problem else []
    for item, got in itertools.zip_longest(items, out):
        if item is None:
            failures.append(("(no request)", "nothing", got))
        elif got != item[2]:
            failures.append((item[1], item[2], "(no answer)" if got is None else got))
    eof_right = 0
    for req, want in AT_EOF:
        got, problem = run_tool(req, timeout=60)
        if got == [want] and not problem:
            eof_right += 1
        else:
            failures.append((req + " (at end of input)", want, f"{got} {problem or ''}".strip()))

    by_label = {}
    for label, _, _, _ in items:
        by_label[label] = by_label.get(label, 0) + 1
    parses = [want for label, req, want, _ in items if req.startswith("parse ")
              and label != "error"]
    accepted = sum(1 for w in parses if w.startswith("OK"))
    compares = [want for label, req, want, _ in items if req.startswith("compare ")
                and label != "error"]
    mutated = sum(1 for item in items if item[3])
    malformed = [got for item, got in zip(items, out) if item[0] == "error"]
    big = sum(1 for w in parses if w.startswith("OK") and
              any(int(x) >= 2 ** 64 for x in w.split("\t")[2:5]))

    lines = [
        "# Test results",
        "",
        "Written by `tests/run_tests.py`. Rerun it to check these numbers.",
        "",
        f"- Oracle: {oracle()}",
        f"- Lean: {lean_version()}",
        f"- Seed: {args.seed}",
        f"- Inputs: {len(items)}",
        f"- Mutated: {mutated} of the inputs are mutated versions",
        "- By kind: " + ", ".join(f"{k} {v}" for k, v in sorted(by_label.items())),
        f"- Strings parsed: {len(parses)}, of which {accepted} accepted and "
        f"{len(parses) - accepted} rejected",
        f"- Accepted versions with a number of 2**64 or more: {big}",
        f"- Pairs compared: {len(compares)}: "
        + ", ".join(f"{k} {compares.count(k)}" for k in ["<", "=", ">", "REJECT"]),
        f"- Malformed requests answered `error`: {malformed.count('error')} of "
        f"{by_label.get('error', 0)}",
        f"- Requests ending in CR LF: every seventh, {len(items) // 7}",
        f"- Last lines sent alone, with no LF or with CR LF, answered right: {eof_right} of "
        f"{len(AT_EOF)}",
        f"- Failures: {len(failures)}",
        "",
    ]
    if failures:
        lines += ["## Failures", ""]
        lines += [f"- `{req[:160]!r}`: expected `{want[:120]!r}`, got `{got[:120]!r}`"
                  for req, want, got in failures[:50]]
        lines.append("")
    write(lines)
    agree = sum(1 for item, got in zip(items, out) if got == item[2])
    print(f"{agree}/{len(items)} requests agree, {len(failures)} failures; results in {RESULTS}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
