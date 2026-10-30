# pep440

A PEP 440 version parser, printer, and precedence comparison in Lean, local versions included, with the round trip proved: parsing the printed form of a well formed version gives the version back.

The specification this follows is PEP 440 (version identification and dependency specification). `SPEC.md` states its rules as this library applies them, including the full ordering key.

## What it does

`Pep440/Version.lean` holds the value type, the well-formedness rule, the printer, and the comparison. A version is an epoch, a list of release numbers, an optional pre-release (one of the kinds a, b, rc, with a number), an optional post-release number, an optional dev-release number, and an optional local part: a list of segments, each a number or a text held lowercase. `Pep440/Parse.lean` holds the parser: an optional leading v, the epoch, the release, then the pre, post, and dev segments in that order, with the PEP spelling tables (alpha reads as a, beta as b, c, pre, and preview as rc), then the local part behind a plus. `Main.lean` is a small command-line front end the tests drive.

## What is proved

The definitions are in `Pep440/Version.lean` and `Pep440/Parse.lean`. The proofs are in `Pep440/Proofs/`.

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed version gives the version back. | `Pep440.Proofs.parse_print` |
| Each step of the example chain printed in PEP 440: 1.0.dev456 < 1.0a1 < 1.0a2.dev456 < 1.0a12.dev456 < 1.0a12 < 1.0b1.dev456 < 1.0b2 < 1.0b2.post345.dev456 < 1.0b2.post345 < 1.0rc1.dev456 < 1.0rc1 < 1.0 < 1.0.post456.dev34 < 1.0.post456 < 1.1.dev1. | `Pep440.Examples.chain_1` to `chain_14` |
| The shorter example chain from the claim: a dev release alone, then with a pre-release, then the pre-release itself; a release, then a post with a dev number, then the post. | `Pep440.Examples.mini_chain_1` to `mini_chain_4` |
| Different spellings of one version compare equal: 1.0 against 1.0.0, 1.0a1 against 1.0.alpha1, a leading v, the c spelling, letter case, leading zeros, the implicit post form. | `Pep440.Examples.eq_release_pad`, `eq_alpha_spelling`, and the rest of that block |
| Example valid texts print back in canonical form, and example invalid texts (an empty release part, a second bang, a pre spelling after a post, whitespace, and more) are rejected. | `Pep440.Examples.reprint_*` and `invalid_*` |
| The local ordering rules: no local part below a local part, a text segment below a number segment, the prefix rule, numbers by value, texts in character order. | `Pep440.Examples.local_absent_first`, `local_text_below_num`, `local_alnum_below_num`, `local_prefix`, `local_num_order`, `local_text_order` |
| Equal spellings of one local part compare equal (letter case, the three separators, leading zeros in a number segment), local texts print back in canonical form, and broken local texts (a bare plus, an empty segment, a second plus, a bad character) are rejected. | `Pep440.Examples.local_eq_*`, `reprint_local_*`, `invalid_local_*` |

A version is well formed when its release list is not empty and its local part is well formed: absent, or at least one segment with every text segment nonempty, held in lowercase letters and digits, and holding at least one letter (a segment of digits only is a number segment). Those are the only conditions the round trip needs: every number prints in canonical decimal by construction, and a held text segment prints as itself, so a printed part always reads back as itself.

The proved theorems check against the standard axioms only (`propext`, `Classical.choice`, `Quot.sound`), which a reader can confirm with the prints in `Pep440/Verify.lean`.

## What is not proved

- That the parser accepts every text the grammar allows, and rejects every text it forbids. The round trip needs neither, so neither is proved. The test harness checks that behaviour against Python's `packaging` library and a strict oracle written from the grammar, and the results file records the outcome, including any failure.
- That `compare` is a full order. The example chains and the equal spellings are proved on concrete texts. Transitivity and totality are not proved, so no claim is made that any two versions compare consistently across a chain of comparisons, beyond the proved examples.
- Version specifiers (`>=`, `~=`, and the rest of PEP 440 beyond the version itself): outside this slice.
- Anything about package indexes, sorting lists of versions, or picking a version.
- Reading requests and printing answers in `Main.lean`: splitting lines, the decimal parser, the semicolon split, and the check that a code is a Unicode scalar value. The tests cover them, malformed requests included.
- Speed. The code works on lists of characters, which suits proofs, not large data.

## What you must trust

- The Lean kernel, which checks the proofs.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about.
- The operating system and hardware it runs on.
- The Python oracles in the test harness: `packaging`, which implements PEP 440, and the strict oracle written from the grammar in `SPEC.md`, and the reader's own reading of PEP 440, which the oracles and this code both follow.

This project has no dependencies beyond Lean itself. The test harness needs Python 3.11 or later and the `packaging` library as its oracle.

## Run it

Needs Linux and [elan](https://github.com/leanprover/elan). Build, then feed request lines to the tool:

```
lake build
echo "parse 49,46,48,97,49" | .lake/build/bin/pep440
```

That request is the text `1.0a1` as character codes, and the answer is `ok:49,46,48,46,97,49`, the codes of the canonical print `1.0.a1`. A text the parser rejects, such as the codes for `1.0+` (a plus with no local part after it), answers `none`. A comparison request puts code 59 between the two texts and answers `lt`, `eq`, or `gt`. A malformed request answers `error`. See `SPEC.md` for the full protocol.

## Re-check it

```
lake build
python3 tests/run_tests.py
```

The test script rebuilds, reruns the fixed cases (the PEP chain, canonical reprints, forbidden texts, local order pairs, each fixed comparison also checked against `packaging`) and the differential run (random spelled versions and pairs against `packaging`, pairs that share one public part so the local key decides, mutated and soup texts against the strict oracle), and rewrites `tests/TEST-RESULTS.md`. The last run, with seed 20261026, recorded 11,620 inputs and 11,620 agreements, with no failures. `packaging` 24.0 was the oracle in that run; the harness checks for it at run time and states which oracle was used in the results file.
