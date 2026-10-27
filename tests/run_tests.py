#!/usr/bin/env python3
"""Tests for the Lean PEP 440 parser, printer, and precedence.

Three parts.

1. Fixed cases. The example ordering chain printed in PEP 440
   as `cmp` requests, valid texts and their canonical reprints
   as `parse` requests, and texts the grammar forbids (each
   must be rejected). Local version texts are fixed cases too:
   valid local parts with their canonical reprints, order
   pairs across the local rules, and the local shapes the
   grammar forbids.

2. A differential run. Python's `packaging` library is the
   oracle for values: it is checked for at the start and its
   version is recorded. Random versions are built part by
   part and spelled in random ways the PEP allows (alias
   spellings, separators, letter case, leading zeros, a
   leading v, implicit post forms); the tool's reprint must be
   the canonical form the SPEC rules give, and `packaging`
   must read the spelled text and the canonical form as the
   same value with the same fields. Random pairs are compared
   for order against `packaging`.

   Where `packaging` prints a value in a different shape than
   this slice's canonical form, that is a named difference,
   recorded in the results with an example. `packaging` also
   accepts surrounding whitespace, which this slice rejects;
   that is the second named difference.

3. Mutated and soup texts, settled by a strict oracle in this
   harness that mirrors the SPEC stage by stage (packaging is
   more lenient there: it trims whitespace, which this slice
   rejects). Malformed request lines must be answered
   `error`.

The strict oracle shares no code with the Lean side. The seed
is recorded in the results file.

    python3 tests/run_tests.py [--seed N] [--count N]

The tool is driven one batch process per chunk of requests:
input written and closed, output drained until the process
exits. The harness builds the executable first, writes
tests/TEST-RESULTS.md, and exits non-zero if any check fails.
It needs Python 3.11 or later.
"""

import argparse
import platform
import random
import subprocess
import sys
import threading
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "pep440"
RESULTS = ROOT / "tests" / "TEST-RESULTS.md"
TIMEOUT = 900
BUILD_TIMEOUT = 3600
CHUNK = 2000

SEED_DEFAULT = 20261026

DIGITS = "0123456789"

try:
    import importlib.metadata

    import packaging
    from packaging.version import InvalidVersion, Version

    PACKAGING_VERSION = importlib.metadata.version("packaging")
except Exception:
    packaging = None
    PACKAGING_VERSION = None


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
# The canonical form, from the SPEC rules: the epoch with a
# bang when above zero, the release numbers dot joined, the
# pre-release as .aN, .bN, or .rcN, the post as .postN, the
# dev as .devN, and the local part as a plus and its segments
# dot joined (a number segment in plain decimal, a text
# segment as held). A value is (epoch, release, pre, post,
# dev, local), with pre a (kind, number) pair or None, and
# local a list of segments or None; a segment is an int for
# a number segment and a str for a text segment.


def canonical(v):
    epoch, release, pre, post, dev, local = v
    out = ""
    if epoch:
        out += f"{epoch}!"
    out += ".".join(str(n) for n in release)
    if pre is not None:
        out += f".{pre[0]}{pre[1]}"
    if post is not None:
        out += f".post{post}"
    if dev is not None:
        out += f".dev{dev}"
    if local is not None:
        out += "+" + ".".join(
            str(seg) if isinstance(seg, int) else seg for seg in local
        )
    return out


# ------------------------------------------------------------------
# The strict oracle, mirroring the SPEC stage by stage: an
# optional leading v, the epoch, the release, then the pre,
# post, and dev segments in that order, then the local part
# behind a plus, and nothing left over. It is the reader for
# mutated and soup texts, where packaging would accept shapes
# this slice rejects.


def lower1(c):
    if "A" <= c <= "Z":
        return chr(ord(c) + 32)
    return c


def take_digits(s, i):
    j = i
    while j < len(s) and s[j] in DIGITS:
        j += 1
    return s[i:j], j


def drop_sep(s, i):
    return i + 1 if i < len(s) and s[i] in ".-_" else i


def opt_num(s, i):
    i = drop_sep(s, i)
    ds, j = take_digits(s, i)
    return (int(ds) if ds else 0), j


def match_word(pat, s, i):
    j = i
    for pc in pat:
        if j >= len(s) or lower1(s[j]) != pc:
            return None
        j += 1
    return j


PRE_TABLE = [
    ("alpha", "a"),
    ("beta", "b"),
    ("preview", "rc"),
    ("pre", "rc"),
    ("rc", "rc"),
    ("a", "a"),
    ("b", "b"),
    ("c", "rc"),
]
POST_TABLE = ["post", "rev", "r"]


ALNUM = set(DIGITS + "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ")


def strict_parse(text):
    s = text
    i = 0
    if i < len(s) and s[i] in "vV":
        i += 1
    epoch = 0
    ds, j = take_digits(s, i)
    if ds and j < len(s) and s[j] == "!":
        epoch = int(ds)
        i = j + 1
    release = []
    while True:
        ds, j = take_digits(s, i)
        if not ds:
            return None
        release.append(int(ds))
        i = j
        if i + 1 < len(s) and s[i] == "." and s[i + 1] in DIGITS:
            i += 1
            continue
        break
    pre = None
    k = drop_sep(s, i)
    for pat, kind in PRE_TABLE:
        m = match_word(pat, s, k)
        if m is not None:
            n, i = opt_num(s, m)
            pre = (kind, n)
            break
    post = None
    if i < len(s) and s[i] == "-" and i + 1 < len(s) and s[i + 1] in DIGITS:
        ds, j = take_digits(s, i + 1)
        post = int(ds)
        i = j
    else:
        k = drop_sep(s, i)
        for pat in POST_TABLE:
            m = match_word(pat, s, k)
            if m is not None:
                n, i = opt_num(s, m)
                post = n
                break
    dev = None
    k = drop_sep(s, i)
    m = match_word("dev", s, k)
    if m is not None:
        n, i = opt_num(s, m)
        dev = n
    local = None
    if i < len(s) and s[i] == "+":
        i += 1
        segs = []
        while True:
            j = i
            while j < len(s) and s[j] in ALNUM:
                j += 1
            seg = s[i:j]
            if not seg:
                return None
            if all(ch in DIGITS for ch in seg):
                segs.append(int(seg))
            else:
                segs.append(seg.lower())
            i = j
            if i < len(s) and s[i] in ".-_":
                i += 1
                continue
            break
        local = segs
    if i != len(s):
        return None
    return (epoch, release, pre, post, dev, local)


def strict_expected(text):
    v = strict_parse(text)
    if v is None:
        return "none"
    return "ok:" + codes(canonical(v))


# ------------------------------------------------------------------
# Fixed cases.

CHAIN = [
    "1.0.dev456",
    "1.0a1",
    "1.0a2.dev456",
    "1.0a12.dev456",
    "1.0a12",
    "1.0b1.dev456",
    "1.0b2",
    "1.0b2.post345.dev456",
    "1.0b2.post345",
    "1.0rc1.dev456",
    "1.0rc1",
    "1.0",
    "1.0.post456.dev34",
    "1.0.post456",
    "1.1.dev1",
]

VALID_REPRINT = [
    ("1.0", "1.0"),
    ("1.0.a1", "1.0.a1"),
    ("1.0.alpha1", "1.0.a1"),
    ("1.0a01", "1.0.a1"),
    ("v1.0", "1.0"),
    ("V2!1.0", "2!1.0"),
    ("1.0c1", "1.0.rc1"),
    ("1.0pre", "1.0.rc0"),
    ("1.0-1", "1.0.post1"),
    ("1.0a1-2", "1.0.a1.post2"),
    ("1.0_a1", "1.0.a1"),
    ("1.0.r", "1.0.post0"),
    ("1.0dev", "1.0.dev0"),
    ("1.0_dev4", "1.0.dev4"),
    ("01!1.0", "1!1.0"),
    ("1.0b2.post345.dev456", "1.0.b2.post345.dev456"),
    ("1!2.0_ALPHA.1-3_dev4", "1!2.0.a1.post3.dev4"),
    ("1.0-post", "1.0.post0"),
    ("1.0+local", "1.0+local"),
    ("1.0a1+ubuntu.1", "1.0.a1+ubuntu.1"),
    ("2!1.0+abc.5", "2!1.0+abc.5"),
    ("1.0.post1+local.2", "1.0.post1+local.2"),
    ("1.0+ABC", "1.0+abc"),
    ("1.0+foo-bar", "1.0+foo.bar"),
    ("1.0+foo_bar", "1.0+foo.bar"),
    ("1.0+007", "1.0+7"),
    ("1.0+0a", "1.0+0a"),
    ("1.0+1a.2b", "1.0+1a.2b"),
]

INVALID = [
    "",
    "1.0..1",
    "1.",
    ".1",
    "1.0a1b2",
    "1.0!",
    "1!1.0!2",
    "1.0-",
    "1.0.post1a1",
    "1.0dev1.post1",
    "1.0_1",
    "1.0--a1",
    " 1.0",
    "1.0 ",
    "1.0a1_2",
    "x1.0",
    "1.0a1.post1-2",
    "1.0al",
    "1..1",
    "vv1.0",
    "1.0+",
    "1.0+a..b",
    "1.0+a.",
    "1.0+.a",
    "1.0+a+b",
    "1.0++a",
    "1.0+a b",
    "1.0+a-b-",
]

LOCAL_CMP = [
    ("1.0", "1.0+1", "lt"),
    ("1.0+abc", "1.0+1", "lt"),
    ("1.0+abc", "1.0+abc.1", "lt"),
    ("1.0+1", "1.0+2", "lt"),
    ("1.0+a1", "1.0+1", "lt"),
    ("1.0+abc", "1.0+abd", "lt"),
    ("1.0+abc.1", "1.0+abc.2", "lt"),
    ("1.0+ABC", "1.0+abc", "eq"),
    ("1.0+foo-bar", "1.0+foo.bar", "eq"),
    ("1.0+007", "1.0+7", "eq"),
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


# ------------------------------------------------------------------
# Random generation: a value, then a spelling of it.


def random_value(rng):
    epoch = rng.choice([0, 0, 0, 1, 2, 7])
    release = [
        rng.choice([0, 1, 2, 9, 10, 42, 365, rng.randrange(0, 10**6)])
        for _ in range(rng.randrange(1, 5))
    ]
    pre = None
    if rng.random() < 0.55:
        pre = (rng.choice(["a", "b", "rc"]), rng.choice([0, 1, 2, 12, 456]))
    post = None
    if rng.random() < 0.35:
        post = rng.choice([0, 1, 3, 345])
    dev = None
    if rng.random() < 0.35:
        dev = rng.choice([0, 1, 34, 456])
    local = random_local(rng) if rng.random() < 0.5 else None
    return (epoch, release, pre, post, dev, local)


def random_local(rng):
    local = []
    for _ in range(rng.randrange(1, 5)):
        if rng.random() < 0.5:
            local.append(rng.choice([0, 1, 2, 7, 42, 2024]))
        else:
            local.append(
                rng.choice(
                    ["abc", "a1", "rc", "x9", "0a", "foo", "bar2",
                     "ubuntu", "a", "zz"]
                )
            )
    return local


def zeros(n, rng):
    return "0" * rng.randrange(0, 3) + str(n)


def num_suffix(n, rng):
    if n == 0 and rng.random() < 0.4:
        return ""
    return rng.choice(["", ".", "-", "_"]) + zeros(n, rng)


def mangle_case(word, rng):
    return "".join(
        c.upper() if rng.random() < 0.4 else c for c in word
    )


def spell(v, rng):
    epoch, release, pre, post, dev, local = v
    out = ""
    if rng.random() < 0.3:
        out += rng.choice("vV")
    if epoch:
        out += zeros(epoch, rng) + "!"
    out += ".".join(zeros(n, rng) for n in release)
    seps = [".", "-", "_", ""]
    pre_num_written = True
    if pre is not None:
        kind, n = pre
        word = rng.choice(
            {
                "a": ["a", "alpha"],
                "b": ["b", "beta"],
                "rc": ["rc", "c", "pre", "preview"],
            }[kind]
        )
        suffix = num_suffix(n, rng)
        pre_num_written = suffix != ""
        out += rng.choice(seps) + mangle_case(word, rng) + suffix
    if post is not None:
        if rng.random() < 0.3 and pre_num_written:
            out += "-" + zeros(post, rng)
        else:
            word = mangle_case(rng.choice(["post", "rev", "r"]), rng)
            out += rng.choice(seps) + word + num_suffix(post, rng)
    if dev is not None:
        out += rng.choice(seps) + mangle_case("dev", rng) + num_suffix(dev, rng)
    if local is not None:
        parts = []
        for seg in local:
            if isinstance(seg, int):
                parts.append(zeros(seg, rng))
            else:
                parts.append(mangle_case(seg, rng))
        out += "+" + parts[0]
        for part in parts[1:]:
            out += rng.choice([".", "-", "_"]) + part
    return out


def mutate(rng, text):
    chars = list(text)
    alphabet = "0123456789aA-.+_;vV !epostdrc"
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


def packaging_value_check(text, v):
    """ packaging must read the text as the generated value."""
    try:
        pv = Version(text)
    except InvalidVersion:
        return f"packaging rejects the spelled text {text!r}"
    cv = Version(canonical(v))
    if pv != cv:
        return f"packaging reads {text!r} as {pv}, not the value of {canonical(v)!r}"
    fields = (pv.epoch, pv.pre, pv.post, pv.dev)
    want = (v[0], v[2], v[3], v[4])
    if fields != want:
        return f"packaging fields for {text!r} are {fields}, not {want}"
    want_local = None
    if v[5] is not None:
        want_local = ".".join(
            str(seg) if isinstance(seg, int) else seg for seg in v[5]
        )
    if pv.local != want_local:
        return f"packaging local for {text!r} is {pv.local!r}, not {want_local!r}"
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=SEED_DEFAULT)
    ap.add_argument("--count", type=int, default=3000)
    args = ap.parse_args()
    rng = random.Random(args.seed)

    if packaging is None:
        print("packaging is not installed; this harness needs it as the oracle")
        return 1

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
    notes = []

    def section(name, pairs):
        sections.append((name, [r for r, _ in pairs], [e for _, e in pairs]))

    fixed_parse = []
    for text, canon in VALID_REPRINT:
        fixed_parse.append((parse_request(text), "ok:" + codes(canon)))
        sv = strict_parse(text)
        if sv is None:
            failures.append(f"fixed parse cases: strict oracle rejects {text!r}")
            continue
        if canonical(sv) != canon:
            failures.append(
                f"fixed parse cases: strict oracle reads {text!r} as "
                f"{canonical(sv)!r}, not {canon!r}"
            )
            continue
        problem = packaging_value_check(text, sv)
        if problem:
            failures.append(f"fixed parse cases: {problem}")
    for text in INVALID:
        fixed_parse.append((parse_request(text), "none"))
        if strict_parse(text) is not None:
            failures.append(f"fixed parse cases: strict oracle accepts {text!r}")
    fixed_parse.append(("parse", "none"))
    fixed_parse.append(("parse ", "none"))
    section("fixed parse cases", fixed_parse)

    cmp_pairs = []
    for a, b in zip(CHAIN, CHAIN[1:]):
        cmp_pairs.append((a, b, "lt"))
        cmp_pairs.append((b, a, "gt"))
    cmp_pairs.append((CHAIN[0], CHAIN[-1], "lt"))
    cmp_pairs.append(("1.0", "1.0.0", "eq"))
    cmp_pairs.append(("1.0a1", "1.0.alpha1", "eq"))
    for a, b, want in LOCAL_CMP:
        cmp_pairs.append((a, b, want))
        if want == "lt":
            cmp_pairs.append((b, a, "gt"))
    fixed_cmp = []
    for a, b, want in cmp_pairs:
        va, vb = Version(a), Version(b)
        got = "lt" if va < vb else "gt" if va > vb else "eq"
        if got != want:
            failures.append(
                f"fixed cmp cases: packaging orders {a!r} against {b!r} "
                f"as {got}, not {want}"
            )
        fixed_cmp.append((cmp_request(a, b), want))
    fixed_cmp.append((cmp_request("1.0+local", "1.0"), "gt"))
    fixed_cmp.append(("cmp 49,59", "none"))
    section("fixed cmp cases", fixed_cmp)

    rand_parse = []
    texts = []
    print_diffs = 0
    print_diff_example = None
    for _ in range(args.count):
        v = random_value(rng)
        text = spell(v, rng)
        texts.append(text)
        rand_parse.append((parse_request(text), "ok:" + codes(canonical(v))))
        problem = packaging_value_check(text, v)
        if problem:
            failures.append(f"random spelled versions, parse: {problem}")
        if str(Version(text)) != canonical(v):
            print_diffs += 1
            if print_diff_example is None:
                print_diff_example = (text, str(Version(text)), canonical(v))
    section("random spelled versions, parse", rand_parse)

    rand_cmp = []
    for _ in range(args.count):
        va_v = random_value(rng)
        vb_v = random_value(rng)
        a = spell(va_v, rng)
        b = spell(vb_v, rng)
        va, vb = Version(canonical(va_v)), Version(canonical(vb_v))
        want = "lt" if va < vb else "gt" if va > vb else "eq"
        rand_cmp.append((cmp_request(a, b), want))
    section("random version pairs, cmp", rand_cmp)

    local_cmp = []
    for _ in range(args.count // 3):
        base = random_value(rng)
        va_v = base[:5] + (random_local(rng),)
        vb_v = base[:5] + (random_local(rng),)
        a = spell(va_v, rng)
        b = spell(vb_v, rng)
        va, vb = Version(canonical(va_v)), Version(canonical(vb_v))
        want = "lt" if va < vb else "gt" if va > vb else "eq"
        local_cmp.append((cmp_request(a, b), want))
    section("random local pairs, cmp", local_cmp)

    mutated = []
    for text in texts:
        m = mutate(rng, text)
        mutated.append((parse_request(m), strict_expected(m)))
    section("mutated texts, parse", mutated)

    soup = []
    soup_alphabet = "01.!-+_abpdevrc "
    for _ in range(args.count // 2):
        n = rng.randrange(0, 15)
        text = "".join(rng.choice(soup_alphabet) for _ in range(n))
        soup.append((parse_request(text), strict_expected(text)))
    section("soup texts, parse", soup)

    section("malformed requests", [(line, "error") for line in MALFORMED])

    lines_out = []
    lines_out.append("# Test results")
    lines_out.append("")
    lines_out.append(
        "Written by `tests/run_tests.py`. Rerun it to check these numbers."
    )
    lines_out.append("")
    lean_version = subprocess.run(
        ["lake", "env", "lean", "--version"], cwd=ROOT,
        capture_output=True, text=True,
    ).stdout.strip()
    lines_out.append(
        f"- Oracle: Python `packaging` {PACKAGING_VERSION} for values and order "
        f"(it is installed in this environment; checked at run time), and a strict "
        f"oracle in the harness mirroring the SPEC for mutated and soup texts "
        f"(Python {platform.python_version()})"
    )
    lines_out.append(f"- Lean: {lean_version}")
    lines_out.append(f"- Seed: {args.seed}")
    lines_out.append("")
    lines_out.append("## Named differences from packaging")
    lines_out.append("")
    lines_out.append(
        "- The canonical print of a pre-release carries a dot in this slice "
        "(for example `1.0.a1`), where packaging prints the same value "
        "without one (`1.0a1`)."
    )
    if print_diff_example is not None:
        t, pv, cv = print_diff_example
        lines_out.append(
            f"  In this run, {print_diffs} of the random spelled versions "
            f"printed differently in packaging; the first was spelled {t!r}, "
            f"packaging prints it as {pv!r}, this slice as {cv!r}."
        )
    lines_out.append(
        "- Packaging accepts surrounding whitespace (for example ` 1.0` "
        "and `1.0 `); this slice rejects both. The fixed parse cases "
        "include both texts and expect rejection."
    )
    lines_out.append(
        "- Local versions are in scope in this slice, and a local part "
        "prints exactly as packaging prints it: lowercase text, "
        "segments dot joined, numbers without leading zeros. Every "
        "print difference in this run traces to the pre-release dot "
        "above; no difference came from a local part."
    )
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
