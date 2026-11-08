# Fidelity referee report: Theorem V (`lean_chi2u`, branch `theorem-v`, commit 08fec84)

Date: 2026-11-08. Referee: Claude (AI), acting as an independent statement-fidelity referee. Scope: does
`Chi2U.V.theoremV : Chi2U.V.TheoremV` say what is claimed, and can anything in the trusted base make it vacuous? The
proofs themselves were not re-reviewed (the kernel checked them). I did not edit any repository file except this one.
My check file and scripts are in my scratchpad (`RefCheckV.lean`, `indep_margin.py`).

**Verdict: PASS WITH FIXES.** The Lean statement is exactly Theorem V of PROOF_V, it depends only on the standard three
axioms, and nothing in the trusted base can weaken it. The required fixes are all documentation: stale docstrings and
stale STATUS.md and CLAUDE.md text that still describe the V ingredients as `sorry` stubs. No Lean change is needed for
correctness.

## 1. Statement fidelity

Elaborated against the built project (`lake build --no-build`: "All targets up-to-date (9124 jobs)"):

```
Chi2U.V.theoremV : Chi2U.V.TheoremV
def Chi2U.V.TheoremV : Prop :=
  ∀ (m : ℕ), 2 ≤ m → m ∉ {3, 5, 7, 9, 15} → Irrational (Chi2U.chi2 (√(↑m ^ 2 + 1) - ↑m))
def Chi2U.chi2 : ℝ → ℝ := fun z => ∑' (n : ℕ), Chi2U.chi2Term z n
def Chi2U.chi2Term : ℝ → ℕ → ℝ := fun z n => z ^ (2 * n + 1) / (2 * ↑n + 1) ^ 2
def Chi2U.zU : ℕ → ℝ := fun mz => √(↑mz ^ 2 + 1) - ↑mz
def Chi2U.TU : ℕ → ℝ := fun mz => Chi2U.chi2 (Chi2U.zU mz)
def Irrational : ℝ → Prop := fun x => x ∉ Set.range Rat.cast
```

* **χ₂.** `Chi2U/Defs.lean` is unchanged since the Theorem U referee report (`git diff fa9fe75 HEAD` is empty for
  `Defs.lean`, `Statement.lean` and `Criterion.lean`). It is Legendre's χ₂(x) = Σ_{n≥0} x^{2n+1}/(2n+1)², with a natural
  exponent (no `rpow`).
* **No junk value.** I proved `Summable (chi2Term (√(m²+1) − m))` for every m ≥ 1 from `summable_chi2Term`,
  `zU_pos` and `zU_lt_one` (`refV_summable`). So for these arguments `chi2` is the genuine sum, with 0 < z_m < 1.
  Irrationality also rules out the `tsum` junk value 0 by itself.
* **Mathlib names.** `Irrational` is Mathlib's, and `√` is `Real.sqrt`. The project defines no `Irrational`, `sqrt`,
  `log`, `Real`, `Finset` or `tsum` of its own (grep).
* **Hypotheses.** They are exactly `2 ≤ m` and `m ∉ ({3, 5, 7, 9, 15} : Finset ℕ)`. There is no `variable` and no
  instance argument. `theoremV` builds `Fact (1 ≤ m)` itself from `2 ≤ m` (`⟨by omega⟩`), so no `Fact` is assumed.
  My checks, all accepted by Lean with standard axioms:
  * `refV_unfold`: `TheoremV ↔ ∀ m, 2 ≤ m → m ∉ {3,5,7,9,15} → Irrational (∑' n, (√(m²+1) − m)^(2n+1)/(2n+1)²)`,
    proved by `Iff.rfl`. So the statement is written with Mathlib primitives only.
  * `refV_plain`: the same conclusion from `2 ≤ m` and `m ≠ 3, 5, 7, 9, 15`.
  * `refV_17`: `Irrational (chi2 (√17 − 4))`, derived from `theoremV 4`.
* **Type of `theoremV`.** `theoremV` really has type `TheoremV` (`#check`).
* **Matches the paper.** The statement is PROOF_V's headline: "for every integer m ≥ 2 with m ∉ E := {3, 5, 7, 9,
  15}, χ₂(√(m²+1) − m) ∉ ℚ".

## 2. Trusted base

* **Axioms.** `#print axioms` in my own file, run against the current build, gives `[propext, Classical.choice,
  Quot.sound]` for all of these: `Chi2U.V.theoremV`, `Chi2U.chi2_sqrt5_sub_two_irrational`,
  `Chi2U.golden_irrational'`, `Chi2U.chi2_sqrt5_sub_two_eq`, `Chi2U.lemmaP`, `Chi2U.V.lemmaP_m`, and all six of my
  `refV_*` checks.
* **Main session's `Axioms.lean` run** (`tasks/b1yk268ns.output`): the 20 lines it holds are all standard, including
  `Chi2U.V.theoremV`, `lemma10nu`, `lemmaS`, `shift_lemma`, `margin_V` and `lemmaP_m`. But the file is missing the
  first 8 of the 28 `#print axioms` lines (`chi2_sqrt5_sub_two_irrational` … `lemma1`). Those lines appear to have
  been cut off when the output was captured. My own run above covers the four headline declarations.
* **Static scan of `Chi2U/` and `Chi2U.lean`.**
  * There is no `sorry`, `admit`, `axiom` declaration, `native_decide`, `implemented_by`, `@[extern]`, `unsafe`,
    `opaque`, `@[csimp]`, `debug.*`/`skipKernelTC`, `ofReduceBool`, `run_cmd`, `#eval`, `notation`/`syntax`/`elab`, or
    `attribute [-instance]`. The single grep hit on "native_decide" is a comment in `Cert/CertU.lean` saying it is not
    used.
  * There is one `macro`: `bsmall_close` in `V/Margin.lean`. It is a new tactic name that expands to
    `unfold PhiL; linarith [...]`. It redefines nothing, and its output is checked by the kernel.
  * The `set_option`s change elaboration only: `exponentiation.threshold 1000` (new, Margin), `maxRecDepth`,
    `backward.isDefEq.respectTransparency false` (PNT port), `lang.lemmaCmd`, and linters.
* **Instances outside PNT.**
  * `fact_one_le_two : Fact (1 ≤ 2)`: global by design, and true.
  * `fact_not_isSquare_d : Fact (¬ IsSquare (dQ mz))`: derived from `Fact (1 ≤ mz)` via the proved
    `not_isSquare_d`. m² + 1 is not a square for m ≥ 1, so this is true.
  * `mI_isMaximal`, `charP_Fl` (NonVan): proved.
  * No instance in `Chi2U/V/`. None of these touches ℝ, `Real.sqrt`, `tsum` or `Irrational`.
* **Root module.** `Chi2U.lean` imports `Chi2U.V.Interface`, and through it every V module. `lake build` is the
  default target.
* **leanchecker.** No replay has been done for the new V modules (TRUST.md's 62-module replay predates them).
  This is optional (see the fixes list).

## 3. The new definitions and the endgame

Each definition checked against PROOF_V:

| Lean (`V/Defs.lean`) | PROOF_V | match |
|---|---|---|
| `nuV m = 1 + v₂(m)` | §0, §1.1: ν = v₂(1 − y) = 1 + v₂(m) | yes |
| `c2V = \|ν − 2\| log 2 / 4` | §0: c₂(ν) | yes |
| `oddDiv m` = odd prime factors of m | §3.2: special primes | yes |
| `cSV = Σ_{p∈oddDiv} (v_p(m)/4 + 1/(4(p−1))) log p` | §0: c_p(e) | yes |
| `alphaV = 4/3 + c2V + cSV` | §0: arithmetic part of M(m) | yes |
| `Lshift = log zU 2 − log zU m` | §5.2, §7: L(m) = log((m + √(m²+1))/(2 + √5)) | yes (1/z_m = m + √(m²+1)) |
| `PhiL = −1.3538792` | Φ_U = −1.35921… | weaker, as documented; `exists_certU'` proves `C.Phi < PhiL` |
| `n2V` (ν ≥ 2): `(ν−1)(h/2−1)² + h⌊log₂h⌋ + 5h − 1 − (h/2)²` in ℕ | §4: (ν−1)(h−2)²/4 − h²/4 + h⌊log₂h⌋ + 5h − 1 | yes (h even). ℕ truncation can only strengthen a proved upper bound. |
| `n2V` (ν = 1): `(h/2−1)² + 3h` | §4 | yes |
| `levelsV h p = {l ∈ [1,h] : p^l ≤ h}` | §3.2: l ≥ 1, p^l < K = h+1 | yes (l ≤ h is automatic) |
| `eS = Σ_l A_K(p^l) + v_p(m)(h/2−1)²` | §3.2: Σ A_K(p^l) + e(h−2)²/4 | yes |

**The endgame needs exactly the listed inputs.** `MachineBounds mz` (MainCond) has these fields:

* `den_int`: `den h · coeff_k(Delta mz h) ∈ ℤ` for all h and k;
* `arith`: `log den h ≤ (α+ε)h²`, eventually along even h;
* `analytic`: `|aeval (TU mz) (Delta mz h)| ≤ exp((β+ε)h²)`, eventually along even h;
* `margin`: `α + β < 0`;
* `nonvan`: for each a/b, infinitely many even h with `Δ_h(a/b) ≠ 0`.

`irrational_of_bounds` feeds these to `irrational_of_poly_approx`, which is unchanged and verbatim from lean_chi2, at
`P h = Δ_{2⌊h/2⌋}`. The same `mz` appears in `Delta mz h`, in `TU mz = chi2 (zU mz)`, and in `DualCertU mz`, whose side
conditions use `vU mz` and `zU mz`. The type forces this, so no mismatch is possible. `zU m = √(m²+1) − m` (printed
above).

**`exists_boundsV` instantiates these fields at the same m:**

* `den := denV m`;
* `α := alphaV m`;
* `β := C'.Phi`, where `C' : DualCertU m` comes from `shift_lemma` applied to `exists_certU'` with
  δ = −M/2;
* `margin`: from `margin_V`, `hC` and `hC'`;
* `analytic := C'.analytic`;
* `nonvan := nonvan_frequently_V m`.

`irrational_of_boundsV` then concludes `Irrational (chi2 (√(m²+1) − m))` by definitional unfolding of `TU`/`zU`.

## 4. The generalised files (stage B2)

* **Theorem U.** Its statement is unchanged. `Statement.lean` has no diff since the initial commit `fa9fe75`.
  `Main.lean` changed only in the proof (`unfold TU; rwa [zU_two]`), and `Golden/**` is unchanged. Its axioms are
  standard (my run).
* **Lemma P′.** `Chi2U.lemmaP : ∀ {mz} [Fact (1 ≤ mz)] {ℓ} [Fact ℓ.Prime], 7 ≤ ℓ → ¬ ℓ ∣ 2*mz → ∀ a {b}, 0 < b →
  ¬ ℓ^2 ∣ b → (Delta mz (3ℓ−1)).eval (a/b) ≠ 0`.
  * The hypotheses are satisfiable. I instantiated both `lemmaP` (mz = 3, ℓ = 7, a/b = 1) and `lemmaP_m` (m = 3,
    ℓ = 7, a/b = 5/7, with 7 ∤ 60 and 49 ∤ 7). Both elaborate with standard axioms (`refV_lemmaP_nonvacuous`,
    `refV_lemmaPm_nonvacuous`).
  * Lean's hypothesis ℓ ∤ 2m is equivalent to PROOF_V's ℓ ∤ m for ℓ ≥ 7. `lemmaP_m` additionally assumes
    ℓ ∤ m² + 1, which makes it a weaker lemma, but harmless.
* **Wiring.** `nonvan_frequently_V` takes a prime ℓ ≥ N + b + 7 + 2m(m²+1). From this it derives ℓ ∤ 2m(m²+1)
  (ℓ is larger than that positive number) and ℓ² ∤ b (ℓ > b), then applies `lemmaP_m` at h = 3ℓ − 1, which is even.
  So `lemmaP_m` is used exactly with these primes.

## 5. Margin

**Repo scripts.** `scripts/margins_lean.py` and `scripts/margin_v_cases.py` (read, then run from a scratch copy with
`python -E -P`; `-I` cannot see the user-site `mpmath`) reproduce `scripts/margins_lean.out`:

* M(m) ≥ 0 for m ∈ [2, 3000] exactly when m ∈ {3, 5, 7, 9, 15};
* the tightest margins are M(11) = −0.012571, M(21) = −0.015023 and M(2) = −0.020546;
* the tail bound for odd m ≥ 69 is −0.001032;
* the bound for even m ≥ 4 is −0.078308.

**Independent check** (`indep_margin.py`, python-flint Arb balls at 300 bits, no shared code). I computed
M(m) = alphaV + PhiL − Lshift/2 directly from the Lean definitions:

* M(m) ≥ 0 is certified exactly for m ∈ {1, 3, 5, 7, 9, 15} among 1 ≤ m ≤ 3000, and no case is undecided;
* M(3), M(5), M(7), M(9), M(15) = +0.3773, +0.2213, +0.1201, +0.1145, +0.0883. These are PROOF_V's values plus
  Φ_L − Φ_U ≈ 0.0053.

**Log bounds used in Margin.lean**, checked with exact arithmetic:

* `log(2+√5) ≤ (25/12) log 2`: (2+√5)¹² = 16692641 + 7465176√5, and 5·7465176² ≤ (2²⁵ − 16692641)² holds in
  integers. The Arb slack is 4.2·10⁻⁴.
* `log 69 ≥ (226/37) log 2`: 2²²⁶ ≤ 69³⁷ holds in integers.
* Mathlib's `log_two_gt_d9` and `log_two_lt_d9` (0.6931471803 < log 2 < 0.6931471808) hold.

**Closed-form constants.**

* K₀ = 0.5279850758 < (1/8) log 69 = 0.5292633.
* Lean's weaker tail bound, 4/3 + Φ_L + (19/24) log 2 − (226/296) log 2, equals −0.0010316 < 0.
* The even case, 4/3 + Φ_L − (1/12) log 2, equals −0.0783 < 0. It follows from a ≥ 2, or from a = 1 with q ≥ 3.

**Coverage.** The finite odd range 11…67 (`bsmall_*`) together with the tail and the even case covers {m ≥ 2} ∖ E. The
exception set is correct.

## 6. Doc and statement mismatches (stale or false text)

1. **`V/Interface.lean`, docstring of `lemmaP_m`:** "The Lean proof of Lemma P′ (`NonVan/**`) is written for `mz = 2`".
   This is false now: `NonVan/**` is generic in `mz`, and `lemmaP_m_proof` is `lemmaP (mz := m)`.
2. **`V/Interface.lean`, docstring of `lemmaS`:** "Needs the multi-level Lemma 8′ (statement in `attic/…`; a
   class-adapted proof … in `../lean_chi2/…`)". This is stale: it is proved in `V/LemmaS.lean` and `V/S*.lean`.
3. **`V/Interface.lean`, "stubs" wording:** section header "Assembly (proved from the stubs)", and the docstrings of
   `exists_boundsV` ("from the stubs") and `theoremV` ("from the stubs"). Also `V/Defs.lean` header ("The stage-B2
   stubs … are in `Interface.lean`"). The ingredients are now proved theorems, so this wording is stale.
4. `V/LemmaS.lean`, `V/Margin.lean` and `V/Shift.lean` each say "the stub `…`". This is cosmetic: it refers to the
   Interface statement that is now a proved theorem.
5. **STATUS.md §"Theorem V port"** (outside `Chi2U/` but load-bearing for readers) says:
   * `Interface.lean` is "not imported by `Chi2U.lean`";
   * `theoremV` is "[Proved from the stubs]";
   * "Stubs (`sorry`)", with a table;
   * "`lake build Chi2U.V.Interface` passes with exactly the six stubs above as `sorry`".

   All four are false at 08fec84. **CLAUDE.md** likewise says "Stage-B2 stubs: `Chi2U/V/Interface.lean` (built
   separately …)". STATUS.md also still says "Not a git repository", which is false.
6. `V/Interface.lean` docstring of `margin_V`: "Numerically: M(m) ≥ 0 exactly on E for m ≤ 3000; closed form beyond".
   This is true, but it reads as if the Lean proof were numerical. The Lean proof covers every m (closed form for even
   m ≥ 4 and odd m ≥ 69, plus case-by-case exact bounds for odd 11…67).
7. README.md and TRUST.md do not mention Theorem V, and `Axioms.lean` lists it. This is not false, but the published
   docs are incomplete. PROOF_V (outside the repo) still says "Not in Lean".

No docstring misstates a Lean *statement*: every displayed formula I checked matches its theorem.

## Required fixes (documentation only)

1. Fix the `lemmaP_m` docstring ("written for `mz = 2`" is false) and the `lemmaS` docstring ("Needs …", attic
   pointer) in `V/Interface.lean`.
2. Remove the "stubs" wording in `V/Interface.lean` (section header, `exists_boundsV`, `theoremV`) and the `V/Defs.lean`
   header.
3. Update STATUS.md §"Theorem V port" and CLAUDE.md: Interface is imported by the root, there are no `sorry`s, and
   Theorem V is proved with standard axioms.

## Optional

* Run `leanchecker` on the new and changed modules (`Chi2U.V.*`, `NonVan/*`, `Cert/CertU`, `Cert/Instance`, `Main`),
  as was done for Theorem U.
* Add Theorem V to README.md and TRUST.md, and update PROOF_V's "Not in Lean".
* Re-run `Axioms.lean` and keep the full output. The captured `b1yk268ns.output` lacks its first 8 lines.
* Consider weakening `lemmaP_m`'s hypothesis to `¬ ℓ ∣ 2 * m`, to match PROOF_V §6 and `lemmaP`. This is cosmetic.
* Rename "the stub `…`" in `V/LemmaS.lean`, `V/Margin.lean` and `V/Shift.lean`.
