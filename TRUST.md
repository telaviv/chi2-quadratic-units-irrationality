# What you have to trust

## Axioms

`lake env lean Axioms.lean` prints, for the main theorems and each of their main ingredients,

```
'Chi2U.V.theoremV' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2U.chi2_sqrt5_sub_two_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2U.golden_irrational'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's three standard axioms, the same ones Mathlib uses. The project contains no `sorry`, no `axiom`
declaration, no `native_decide`, no `implemented_by` and no `@[extern]`, so nothing relies on the compiler. Every
numerical check is done by the kernel:
- the dual certificate of Theorem B′ is a decidable statement about rational data, proved by `decide +kernel`
  (`Cert/CertU.lean`, 16 chunks of grid cells, a log table of 2004 entries, the energy bound, the tail);
- the dyadic enclosure of `log 2` used by the log table is proved by `decide +kernel` (`Interval/Log.lean`).

## Environment replay

**Theorem V (2026-11-08).** After the files for general m were added (76 modules), every module was replayed again with
the command below: all 76 modules pass (≈ 52 minutes; `scripts/leanchecker_v.log`). The record for Theorem U follows.

`lake build` checks each declaration in the kernel as it is added. To avoid trusting the elaborator's handling of the
stored environment, every declaration of all 62 project modules was also replayed through the kernel with `leanchecker`
(shipped with the Lean toolchain), on 2026-11-07:

```sh
for m in $(find Chi2U -name "*.lean" | sed 's/\.lean$//; s#/#.#g'); do lake env leanchecker "$m"; done
```

All 62 modules pass (≈ 42 minutes in total; per-module results and timings in `scripts/leanchecker.log`). After a
docstring-only edit to `Statement.lean`, that module was rebuilt and `Statement`, `Main` and `Golden.Corollary` were
replayed again; all pass. Each module is replayed against the compiled environment of its imports, so Mathlib itself is
not re-checked (that would need `leanchecker --fresh`, which has not been run). An independent fidelity referee
(`FIDELITY_REFEREE.md`) also checked that the statements are faithful; a second one (`FIDELITY_REFEREE_V.md`) did the
same for Theorem V (PASS WITH FIXES; the fixes were docstrings, applied) and re-derived the exception set {3, 5, 7, 9, 15}
in interval arithmetic for m ≤ 3000.

## Fresh-clone check

This check was made for Theorem U, before the files for general m were added (the complete project now has 9124 jobs;
a fresh-clone check of it has not been run yet). On 2026-11-07 the repository was cloned into an empty folder and checked from scratch with the commands of the README,
on Windows 11 Home with 32 logical processors and 31.7 GB of RAM:

| step | result | time |
|---|---|---|
| `lake exe cache get` | Mathlib v4.35.0 downloaded and unpacked | 8 min 24 s |
| `LEAN_NUM_THREADS=4 lake build` | `Build completed successfully (9110 jobs)`, no errors | 9 min 35 s |
| `lake env lean Axioms.lean` | all 22 listed declarations: `[propext, Classical.choice, Quot.sound]` | 20 s |

The clone was of commit `29bf98e`. Recording this result (in this file, the README and the paper's §9.6) is the only
change since; no Lean file changed.

## The statements

The kernel checks the proof. It cannot check that the statements mean what we claim, so read these definitions:

| file | definition |
|---|---|
| `Chi2U/Defs.lean` | `chi2Term z n := z^(2n+1) / (2n+1)²`, `chi2 z := ∑' n, chi2Term z n`, with `summable_chi2Term` for `|z| ≤ 1` (so the `tsum` is the genuine sum of the series). Copied verbatim from [chi2-irrationality](https://github.com/telaviv/chi2-irrationality) (only the namespace differs). |
| `Chi2U/Statement.lean` | `TheoremU := Irrational (chi2 (Real.sqrt 5 - 2))` |
| `Chi2U/V/Defs.lean` | `V.TheoremV := ∀ m : ℕ, 2 ≤ m → m ∉ ({3, 5, 7, 9, 15} : Finset ℕ) → Irrational (chi2 (Real.sqrt ((m : ℝ) ^ 2 + 1) - m))` (proved as `V.theoremV` in `V/Interface.lean`) |
| `Chi2U/Golden/Corollary.lean` | `golden_irrational : Irrational (π^2/24 - 3/4 * log goldenRatio ^ 2)`, `golden_irrational' : Irrational (π^2 - 18 * log goldenRatio ^ 2)` |

`Irrational` is Mathlib's (`x ∉ Set.range ((↑) : ℚ → ℝ)`); `goldenRatio` is Mathlib's `(1 + √5)/2`. The closed form
`chi2 (√5 − 2) = π²/24 − ¾ log²φ` is itself proved (`Golden/ClosedForm.lean`, via Landen's identity for χ₂ and Euler's
reflection and Landen's identity for the dilogarithm), so the golden-ratio corollaries are not separate assumptions.

Since 0 < √(m² + 1) − m < 1, `chi2` is again the genuine sum of the series. Everything in between (the machine `Δ_h`
over ℚ(√(m² + 1)), the constants `alphaV`, `Lshift`, `PhiL`, the denominators, the certificate) is internal to the proof.

## Generated files

`Chi2U/Cert/DataU.lean` contains literal data produced by `scripts/gen_cert_u.py` (run as
`python scripts/gen_cert_u.py 50 8 4 Chi2U/Cert/DataU.lean`). The script and its output are **untrusted inputs**: every
number is re-checked by the kernel, so a wrong value makes the build fail; it cannot make a false theorem true.

## Who checked what

The construction, the written proof (the working notes behind the paper in `paper/`), the paper and this formalisation
were produced by AI models (Claude). The written proof of Theorem U was read by one AI gate referee (PASS WITH FIXES, fixes applied),
and the paper by a whole-chain AI referee (PASS after minor revisions, applied). The written proof of Theorem V was read
by one AI gate referee (PASS WITH FIXES, fixes applied); the revised paper, which adds Theorem V, has not yet had a
whole-paper referee. The statements were checked by the
fidelity referee above. Apart from the Lean kernel check, **no human has reviewed the mathematics or the Lean code**.
