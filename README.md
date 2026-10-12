# Proof of Hardin's empirical column recurrences for OEIS A246737

[![Lean build](https://github.com/het4rk/OEIS-A246737-proof/actions/workflows/lean.yml/badge.svg)](https://github.com/het4rk/OEIS-A246737-proof/actions/workflows/lean.yml)

**Author:** Hetark Shah, AI-assisted by Grok  
**Date:** October 12, 2026

## Result

Let `T(n,k)` be the number of length `n+4` arrays over `0..k` with no pair in any five consecutive terms summing to exactly `k` ([A246737](https://oeis.org/A246737), R. H. Hardin, 2014). We prove, for all `n ≥ 0` (over ℤ):

- **every odd `k`** (order 8): `T(n+8) = (k−3)T(n+7) + 4T(n+6) + (k−3)T(n+5) + (k²−6k+11)T(n+4) + (3k−9)T(n+3) − (k−3)T(n+1) − T(n)`
- **every even `k`** (order 24): `T(n+24) = Σ c_i(k) T(n+i)` with explicit coefficients `c_i ∈ ℤ[k]` of degree ≤ 5 (see `T_even_int` and Table 1 of the paper).

As corollaries we prove all of Hardin's "Empirical for column k" formulas for `k = 1..7, 9` verbatim (the `k = 4, 6` ones as written out in A246733 and A246735), and for `k = 8`, where the entry only says "[order 24]", we give and prove the explicit order-24 recurrence.

The method is a transfer-matrix argument on 35 types of quadruples, uniform in `k`, extending the type reductions from our [A245995](https://github.com/het4rk/OEIS-A245995-proof) and [A246479](https://github.com/het4rk/OEIS-A246479-proof) proofs. The naive transfer matrix has Θ(k⁴) states. What this repo adds is the 35-type reduction, the uniform-in-`k` recurrences, and a machine-checked proof. No published proof was found (OEIS and web search, October 12, 2026; all formulas in A246737 and A246732–A246736 are still marked "Empirical").

## Status

**Complete proof** of Hardin's nine column formulas and the two general recurrences. Machine-checked. Not covered: minimality of the recurrences, Hardin's row recurrences, Barker's empirical generating functions, and the row closed forms in A246738/A246739 (see the paper's Limitations section).

## Theorems and Lean names

| Lean name | Statement |
|---|---|
| `good_cons`, `N_succ` | prepending a letter (one-step recursion) |
| `step`, `typ_step`, `N_eq_typ` | counts depend only on the quadruple type (35 types) |
| `T_eq_F` | `T` in terms of the type values |
| `T_odd_int`, `T_even_int` | the general recurrences |
| `T_col1` … `T_col9` | Hardin's column formulas in OEIS indexing |

No `sorry` and no `native_decide`. `scripts/check_bfile.py` checks the recursion against all 1661 terms of Hardin's b-file.

## Build

Toolchain `leanprover/lean4:v4.35.0-rc4`; Mathlib `v4.35.0-rc4` (pinned in `lake-manifest.json`).

```bash
cd A246737
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Axioms output

All 12 theorems in `Axioms.lean` report `[propext, Classical.choice, Quot.sound]` (see `verification/axioms.txt`).

## Machine-check attestation

- [`verification/`](verification/): `build-log.txt`, `axioms.txt`, and [`VERIFICATION.md`](verification/VERIFICATION.md).
- [CI](https://github.com/het4rk/OEIS-A246737-proof/actions/workflows/lean.yml) does a clean build on every push, fails on any `sorry`, checks the axiom whitelist, and uploads the `lean-attestation` artifact.

## Paper

[`paper/main.tex`](paper/main.tex) and [`paper/paper.pdf`](paper/paper.pdf).

## Citation

> Hetark Shah (AI-assisted by Grok), *A proof of Hardin's empirical column recurrences for OEIS A246737, formalized in Lean 4*, 2026. https://github.com/het4rk/OEIS-A246737-proof

## License

Apache-2.0 (the same as Mathlib). See [`LICENSE`](LICENSE).
