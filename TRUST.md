# What you have to trust

## Axioms

`lake env lean Axioms.lean` prints, for the main theorems and each of their main ingredients,

```
'Chi2U.V.theoremV' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2U.VOdd.theoremVOdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2U.Ti.theoremVi' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2U.chi2_sqrt5_sub_two_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2U.golden_irrational'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

and the same list for each of the 42 declarations in `Axioms.lean` (the output of the run for Theorem V_i is
`scripts/axioms_ti.txt`). These are Lean's three standard axioms, the same ones Mathlib uses. The project contains no `sorry`, no `axiom` declaration, no `native_decide`, no `implemented_by` and
no `@[extern]`, so nothing relies on the compiler. Every numerical check is done by the kernel with `decide +kernel`:
- Theorem U's dual certificate (Theorem B′) is a decidable statement about rational data: `Cert/DataU.lean` (the cells
  of the grid 1/40 on [0, 4] in 4 chunks of 40, the energy bound, the tail, the enclosure of log z), with the shared table
  of 1004 logarithm enclosures in `Cert/LogTab.lean`; `Cert/CertU.lean` states the result;
- the 11 direct certificates of Theorem V_odd, in the same format (`VOdd/CertData/A*.lean`, with the same log table);
- the margin cases of Theorem V_odd (`VOdd/Margin.lean`: the `logPt` enclosures of the logarithms, and `finL_mem`, which
  says that the list of 96 checked cases contains every odd a < 275 outside 𝓔_odd);
- the margin cases of Theorem V_i (`Ti/Margin.lean`: the `logPt 30` enclosures of the logarithms in the 113 cases
  `M_n`, and `finL_mem`, which says that the list `finL` of checked cases contains every n < 275 not covered by the
  three closed forms and outside the exception set: the n ≡ 2 mod 4 with 22 ≤ n < 138, n ≠ 30, and the odd
  71 ≤ n < 275 outside `EOddI`);
- the dyadic enclosure of `log 2` used by the log table (`Interval/Log.lean`).

Theorem V_i adds no certificate: it uses Theorem U's, moved to each point by the shift lemma.

## Environment replay

**Theorem V_i (2026-11-09).** After the files for Ti₂ were added (130 modules), every module was replayed again with
the command below: all 130 modules pass (3383 s ≈ 56 min; `scripts/leanchecker_vi.log`).

**Theorem V_odd (2026-11-09).** After the files for odd traces were added (95 modules), every module was replayed again
with the command below: all 95 modules pass (9621 s ≈ 2 h 40 min, of which 999 s for the first module, read from a cold
disk; `scripts/leanchecker_vodd.log`).

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
not re-checked by these per-module replays. **Fresh replay (2026-11-09):** `lake env leanchecker --fresh Chi2U` replays
the whole environment of the root module from scratch, Mathlib included; it passes (exit code 0, 2499 s ≈ 42 min;
`scripts/leanchecker_fresh.log`), at commit 5246009 (Lean files as of bfba108).

## Fresh-clone check

This check was made for Theorem U, before the files for general m, for odd traces and for Ti₂ were added (the complete
project now has 9178 jobs and 130 modules; a fresh-clone check of it has not been run yet). On 2026-11-07 the repository was cloned into an
empty folder and checked from scratch with the commands of the README, on Windows 11 Home with 32 logical processors and
31.7 GB of RAM:

| step | result | time |
|---|---|---|
| `lake exe cache get` | Mathlib v4.35.0 downloaded and unpacked | 8 min 24 s |
| `LEAN_NUM_THREADS=4 lake build` | `Build completed successfully (9110 jobs)`, no errors | 9 min 35 s |
| `lake env lean Axioms.lean` | all 22 listed declarations: `[propext, Classical.choice, Quot.sound]` | 20 s |

The clone was of commit `29bf98e`.

## The statements

The kernel checks the proof. It cannot check that the statements mean what we claim, so read these definitions:

| file | definition |
|---|---|
| `Chi2U/Defs.lean` | `chi2Term z n := z^(2n+1) / (2n+1)²`, `chi2 z := ∑' n, chi2Term z n`, with `summable_chi2Term` for `|z| ≤ 1` (so the `tsum` is the genuine sum of the series). Copied verbatim from [chi2-irrationality](https://github.com/telaviv/chi2-irrationality) (only the namespace differs). |
| `Chi2U/Statement.lean` | `TheoremU := Irrational (chi2 (Real.sqrt 5 - 2))` |
| `Chi2U/V/Defs.lean` | `V.TheoremV := ∀ m : ℕ, 2 ≤ m → m ∉ ({3, 5, 7, 9, 15} : Finset ℕ) → Irrational (chi2 (Real.sqrt ((m : ℝ) ^ 2 + 1) - m))` (proved as `V.theoremV` in `V/Interface.lean`) |
| `Chi2U/VOdd/Defs.lean` | `VOdd.EOdd : Finset ℕ := {5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33, 35, 37, 39, 41, 43, 45, 47, 49, 51, 53, 55, 57, 63, 65, 69, 75, 77, 81, 85, 87, 93, 99, 105, 165}` (39 values), `VOdd.TheoremVOdd := ∀ a : ℕ, Odd a → 5 ≤ a → a ∉ EOdd → Irrational (chi2 ((Real.sqrt ((a : ℝ) ^ 2 + 4) - a) / 2))` (proved as `VOdd.theoremVOdd` in `VOdd/Interface.lean`) |
| `Chi2U/Ti/Defs.lean` | `Ti.ti2Term z k := (-1)^k * z^(2k+1) / (2k+1)²`, `Ti.Ti2 z := ∑' k, ti2Term z k` (the inverse tangent integral), `Ti.EOddI : Finset ℕ := {75, 77, 81, 85, 87, 91, 93, 95, 99, 105, 111, 117, 123, 135, 147, 165, 195}` (17 values), `Ti.TheoremVi := (∀ m : ℕ, 4 ≤ m → m ∉ ({5, 7, 9, 15} : Finset ℕ) → Irrational (Ti2 (m - Real.sqrt ((m : ℝ) ^ 2 - 1)))) ∧ (∀ n : ℕ, Odd n → 71 ≤ n → n ∉ EOddI → Irrational (Ti2 ((n - Real.sqrt ((n : ℝ) ^ 2 - 4)) / 2)))` (proved as `Ti.theoremVi` in `Ti/Interface.lean`). `Ti2` does not depend on `chi2`. |
| `Chi2U/Golden/Corollary.lean` | `golden_irrational : Irrational (π^2/24 - 3/4 * log goldenRatio ^ 2)`, `golden_irrational' : Irrational (π^2 - 18 * log goldenRatio ^ 2)` |

`Irrational` is Mathlib's (`x ∉ Set.range ((↑) : ℚ → ℝ)`); `goldenRatio` is Mathlib's `(1 + √5)/2`. The closed form
`chi2 (√5 − 2) = π²/24 − ¾ log²φ` is itself proved (`Golden/ClosedForm.lean`, via Landen's identity for χ₂ and Euler's
reflection and Landen's identity for the dilogarithm), so the golden-ratio corollaries are not separate assumptions.

Since 0 < √(m² + 1) − m < 1 and 0 < (√(a² + 4) − a)/2 < 1, `chi2` is again the genuine sum of the series in Theorems V
and V_odd. The statement of Theorem V_odd is written with (√(a² + 4) − a)/2 directly; the internal point `zU a` is
rewritten into this form by a proved lemma (`zU_eq_half`). Likewise `Ti/PoleExpansion.lean` proves `summable_ti2Term`
for |z| ≤ 1, and 0 < `zT n` < 1 (`zT_pos`, `zT_lt_one` in `Ti/Field.lean`), so `Ti2` is the genuine sum of its series
at every point of Theorem V_i (in any case a non-summable `tsum` is 0, which is rational). The statement of Theorem V_i
is written with m − √(m² − 1) and (n − √(n² − 4))/2 directly; the internal point `zT n = n/2 − √((n/2)² − 1)` is
rewritten into these forms by proved lemmas (`zT_two_mul`, `zT_eq_half`). Everything in between (the machines `Δ_h`
over ℚ(√(a² + 4)) and over ℚ(√((n/2)² − 1)), the constants `alphaV`, `Lshift`, `PhiL`, `alphaO`, `betaO`, `PhiC`, `zT`,
`c2T`, `alphaT`, `LshiftT`, `betaT`, the predicate `marginOK`, the list `certA`, the denominators, the certificates) is
internal to the proof: a wrong internal definition could make the proof fail, not make a statement weaker.

## Generated files

These files contain literal data produced by Python scripts. The scripts and their output are **untrusted inputs**:
every number is re-checked by the kernel, so a wrong value makes the build fail; it cannot make a false theorem true.

| file | generator |
|---|---|
| `Chi2U/Cert/DataU.lean`, `Chi2U/Cert/LogTab.lean` | `python scripts/gen_cert_u.py` (no arguments; it runs `scripts/gen_cert_lin.py 4 10 8 4 --tab LogTab.tab 1004 Chi2U/Cert/LogTab.lean --tabout --checkfull --checktab --chunk 40 --lean Chi2U/Cert/DataU.lean --ns Chi2U.Cert.DataU`) |
| `Chi2U/VOdd/CertData/A*.lean` (11 files) | `python scripts/gen_cert_lin.py a N s 4 --tab LogTab.tab 1004 Chi2U/Cert/LogTab.lean --chunk 40 --lean Chi2U/VOdd/CertData/A<a>.lean --ns Chi2U.VOdd.CertData.A<a>`, with (N, s) and the chunk size as recorded in the first line of each file |
| the case section of `Chi2U/VOdd/Margin.lean` | `python scripts/margin_vodd_cases.py --gen` |
| the case section of `Chi2U/Ti/Margin.lean` (between `BEGIN GENERATED` and `END GENERATED`) | `python scripts/ti/margin_ti_cases.py --gen` |
| the exponents of the finite cases of `Chi2U/V/Margin.lean` | `python scripts/margin_v_cases.py` (writes `cases.json`) |

## Who checked what

The construction, the written proofs (the working notes behind the paper in `paper/`), the paper and this formalisation
were produced by AI models (Claude). The written proof of Theorem U was read by one AI gate referee (PASS WITH FIXES,
fixes applied), and the paper by a whole-chain AI referee (PASS after minor revisions, applied). The written proofs of
Theorem V, Theorem V_odd and Theorem V_i were each read by one AI gate referee (PASS WITH FIXES, fixes applied; for
Theorem V_i the referee read the first write-up, and the delta proof written afterwards to apply the fixes was not
re-read); the paper with Theorem V and its extensions was read by further whole-paper AI referees. The fidelity of the Lean statements was
checked by four independent AI referees: `FIDELITY_REFEREE.md` (Theorem U, PASS), `FIDELITY_REFEREE_V.md` (Theorem V,
PASS WITH FIXES; the fixes were docstrings, applied; it re-derived the exception set {3, 5, 7, 9, 15} in interval
arithmetic for m ≤ 3000), `FIDELITY_REFEREE_VODD.md` (Theorem V_odd, PASS WITH FIXES; the fixes were documentation only,
in this file, the README and the paper, applied; it compared `EOdd` with the paper element by element and recomputed the
exception set for odd a ≤ 6001, with Lean's constants and with the paper's) and `FIDELITY_REFEREE_VI.md` (Theorem V_i,
PASS WITH FIXES; the fixes were committing a wiring file that the referee found only in the working tree, and
documentation in this file, the README and the paper, applied; it compared `EOddI` with the paper element by element and
recomputed the exception set for 5 ≤ n ≤ 5000 in interval arithmetic, with Lean's constants and with the paper's, by code
that shares nothing with the generator). Apart from the Lean kernel check, **no human has reviewed the mathematics or
the Lean code**.
