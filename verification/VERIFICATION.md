# Verification record

| Item | Value |
|---|---|
| Date | 2026-10-12 |
| Verified commit | `5233729e626a5f3791b5c6bf512f3c92bbc62778` |
| Lean toolchain | `leanprover/lean4:v4.35.0-rc4` |
| Mathlib | `v4.35.0-rc4`, commit `1f414401f69059aa7eead47b53ee40bd38455eeb` |
| Build result | `Build completed successfully (9036 jobs)` (see [`build-log.txt`](build-log.txt)) |
| Axioms | 12 declarations, all `[propext, Classical.choice, Quot.sound]` (see [`axioms.txt`](axioms.txt)) |
| CI | run #1 on `5233729e626a5f3791b5c6bf512f3c92bbc62778`: success. [![Lean build](https://github.com/het4rk/OEIS-A246737-proof/actions/workflows/lean.yml/badge.svg)](https://github.com/het4rk/OEIS-A246737-proof/actions/workflows/lean.yml) |

## Reproduce

```bash
git clone https://github.com/het4rk/OEIS-A246737-proof
cd OEIS-A246737-proof
git checkout 5233729e626a5f3791b5c6bf512f3c92bbc62778
cd A246737
lake exe cache get
lake build
lake env lean Axioms.lean
grep -rnwE 'sorry|native_decide' A246737 --include=*.lean   # expect no output
```

## Fresh-clone check

A fresh clone of that commit was built with `lake exe cache get` and `lake build` (success). `lake env lean Axioms.lean` was checked with `scripts/check_axioms.sh`, which reported OK for 12 declarations. `grep` finds no `sorry` or `native_decide`.

## b-file check

`scripts/check_bfile.py` reproduces all 1661 terms of Hardin's b-file (b246737.txt) from the 35-type recursion.

## SHA-256 of the Lean sources (at the verified commit)

```
204d4fb8736fc93eef91db0e85c3b94c8bd996c92829566c22a069ebdc0798be  A246737.lean
740d6519acbac4c64bdb9c4abae17f4fc6d667e656f8ef5251edea18b6c7e9d2  Axioms.lean
79c6ec21c3f3d34eb9c819687de456e4994d7b47e5e79e0fa943339cedc30d70  A246737/Basic.lean
ec12362a0c492faf46bef40dd53dcbe2d6e1b9273c086a80b63ab19fc08f0869  A246737/EvenBase.lean
29f613f3794833b24f8fb1e007b13b3eb18b996130bf58d49f50b06a1e3d8056  A246737/EvenChain0.lean
449d16965453508c4139d897fb06b6551a4168e318c88bc214b2730d6c572b72  A246737/EvenChain1.lean
67ecea8086cf5abceeb952f18490a60ef343cc68b58cc86fa15e1172a7be65a9  A246737/EvenChain2.lean
6d01ee6392391201ea19d52af3c2da9071e1779ad5b2569ad3668d210fc45418  A246737/EvenChain3.lean
27f4503dfc2e66b16876e466627d79e35c3171f09d935860dccd4f423010779b  A246737/EvenChain4.lean
52af8e46aca8d2d4b69be28181ed41f1131023543c4c9cde87e16a563eb4e698  A246737/FormsEven.lean
2d206036b3d4d527fd953c90db38481b78c9e041767303765b64b9f9d06680b8  A246737/FormsOdd.lean
67e0bf4f7e029afc2c66bd4b81e30e7ab1027f71f5af4b780dc1ec8dcdf9cab1  A246737/FormsSmall.lean
ae23195a52eea9031dac33485d3f0b3839fa55710d9857ff9c226984fdce3b67  A246737/Main.lean
09644741717a46ed5f14de9551d9e329d46f042524850a6633848cb69d37bfda  A246737/Step.lean
08040ae44cfb9a66ae7ae0d9a29583fa7f960c4499c3754beb09a26d881323bd  A246737/StepGen.lean
48d642a11bc8fe4ab57a611806c5347da873b2366da1c20f835d8b99173732fc  A246737/Sums.lean
56a574469b40cb426092b6e81d2a11326a7442f737dd05b4e5ed0d668402172d  A246737/Types.lean
e8b72c2bc8c1b582fb555621256d987556fe94ec7d0605161f5e0371e2dd5aeb  lakefile.toml
56a88a3942925b1a87aa76ca52367191344059446d8ec7f95ec470829621c283  lake-manifest.json
8f89aa44fccdb1a0b6cc768c7c9f54b94cd40e47a08d582f82d1235f13075cf7  lean-toolchain
```
