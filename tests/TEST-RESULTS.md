# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python `packaging` 24.0 for values and order (it is installed in this environment; checked at run time), and a strict oracle in the harness mirroring the SPEC for mutated and soup texts (Python 3.12.3)
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261026

## Named differences from packaging

- The canonical print of a pre-release carries a dot in this slice (for example `1.0.a1`), where packaging prints the same value without one (`1.0a1`).
  In this run, 1667 of the random spelled versions printed differently in packaging; the first was spelled '2.00862067_ALpha-000', packaging prints it as '2.862067a0', this slice as '2.862067.a0'.
- Packaging accepts surrounding whitespace (for example ` 1.0` and `1.0 `); this slice rejects both. The fixed parse cases include both texts and expect rejection.
- Packaging accepts local versions (for example `1.0+local`); local versions are out of this slice's scope and are rejected. The fixed parse cases include four local texts and expect rejection for each.

- fixed parse cases: 44 inputs, 44 agreements
- fixed cmp cases: 33 inputs, 33 agreements
- random spelled versions, parse: 3000 inputs, 3000 agreements
- random version pairs, cmp: 3000 inputs, 3000 agreements
- mutated texts, parse: 3000 inputs, 3000 agreements
- soup texts, parse: 1500 inputs, 1500 agreements
- malformed requests: 12 inputs, 12 agreements
- Total: 10589 inputs, 10589 agreements
- Failures: 0
