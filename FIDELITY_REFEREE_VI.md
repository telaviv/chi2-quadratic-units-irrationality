# Fidelity referee report: Theorem V_i (`Chi2U.Ti.theoremVi`)

Referee: independent AI fidelity referee (Claude), 2026-11-09. Branch `theorem-vi`, HEAD `e0d271e` ("Theorem V_i
complete in Lean") plus one uncommitted change in the working tree: `Chi2U/Ti/Interface.lean` adds
`import Chi2U.Ti.NonVan` and replaces the `sorry` of `lemmaP_n` by `lemmaP_n_proof`. I did not build anything. I read the
output that the running build wrote to `scripts/axioms_ti.txt`. Scope: what is new for V_i. The ingredients of U, V and
V_odd were not re-checked (see `FIDELITY_REFEREE_V.md`, `FIDELITY_REFEREE_VODD.md`).

**Verdict: PASS WITH FIXES.** The Lean statement `TheoremVi` is exactly the paper's Theorem V_i (PROOF_TI2 §0; main.tex
Theorem 8.x `thm:Vi`, l. 203–214). The exception set is the same element by element. There are no hidden hypotheses,
the trusted base is unchanged, and `#print axioms Chi2U.Ti.theoremVi` gives `[propext, Classical.choice, Quot.sound]`.
One fix is required in the repository, not in the mathematics: **the committed HEAD still has a `sorry`** (R1).
The other required fixes are documentation (R2–R4).

---

## 1. Statement fidelity: faithful

`Chi2U/Ti/Defs.lean`:

```lean
noncomputable def ti2Term (z : ℝ) (k : ℕ) : ℝ := (-1) ^ k * z ^ (2 * k + 1) / (2 * (k : ℝ) + 1) ^ 2   -- l. 27
noncomputable def Ti2 (z : ℝ) : ℝ := ∑' k : ℕ, ti2Term z k                                            -- l. 30
def EOddI : Finset ℕ := {75, 77, 81, 85, 87, 91, 93, 95, 99, 105, 111, 117, 123, 135, 147, 165, 195}     -- l. 35–36
def TheoremVi : Prop :=                                                                                 -- l. 42–44
  (∀ m : ℕ, 4 ≤ m → m ∉ ({5, 7, 9, 15} : Finset ℕ) → Irrational (Ti2 (m - Real.sqrt ((m : ℝ) ^ 2 - 1)))) ∧
  (∀ n : ℕ, Odd n → 71 ≤ n → n ∉ EOddI → Irrational (Ti2 ((n - Real.sqrt ((n : ℝ) ^ 2 - 4)) / 2)))
```

* **Function.** The term parses as ((−1)^k · z^{2k+1}) / (2k+1)², all in ℝ. So `Ti2 z = Σ_{k≥0} (−1)^k z^{2k+1}/(2k+1)²`,
  which is Lewin's inverse tangent integral as defined in PROOF_TI2 §0 and main.tex l. 204.
* **Convergence.** `summable_ti2Term : |z| ≤ 1 → Summable (ti2Term z)` (`Ti/PoleExpansion.lean` l. 34–40, by comparison
  with Σ 1/(k+1)² via `abs_chi2Term_le`). It is used in `hasSum_ti2Term_zT : HasSum (ti2Term (zT n)) (TT n)`
  (l. 53–54) with `zT_pos`, `zT_lt_one` (`Ti/Field.lean` l. 161, 169). So the `tsum` is the true sum at every point the
  theorem talks about. Even without that lemma the statement could not be vacuous in this way: a non-summable `tsum`
  is 0, which is rational, so `Irrational (Ti2 x)` itself implies that the series at x is summable.
* **Points.** Part (a) is literally Ti₂(m − √(m²−1)) and part (b) is literally Ti₂((n − √(n²−4))/2), both real-valued
  (`↑m`, `↑n` are coerced to ℝ because `Real.sqrt` fixes the type). The statement does not use `zT`. The bridges
  `zT_eq_half : zT n = (n − √(n²−4))/2` (l. 54–60) and `zT_two_mul : zT (2m) = m − √(m²−1)` (l. 62–63), with
  `zT n := n/2 − √((n/2)² − 1)` (l. 52), are proved, not assumed. They are used only in the last lines of
  `theoremVi` (`Interface.lean` l. 293, 303) to rewrite `Ti2 (zT n)`.
* **Quantifiers and ranges.** (a) `m : ℕ`, `4 ≤ m`, `m ∉ {5, 7, 9, 15}` is the paper's "every integer m ≥ 4 with
  m ∉ {5,7,9,15}". (b) `Odd n`, `71 ≤ n`, `n ∉ EOddI` is the paper's "every odd integer n ≥ 71 with n ∉ 𝓔_i". There are
  no instance arguments, and the `Fact (3 ≤ n)` instance is built inside the proof (`irrational_Ti2_zT`, l. 275).
* **Exception set.** `EOddI` = {75, 77, 81, 85, 87, 91, 93, 95, 99, 105, 111, 117, 123, 135, 147, 165, 195}. I compared it
  element by element with PROOF_TI2 §0 (E_odd, 17 values, all ≤ 195) and main.tex l. 205–207 (𝓔_i). All three are identical.
* **Vacuity.** None. `Irrational` is Mathlib's, and infinitely many m and n satisfy the hypotheses.

## 2. Trusted base: unchanged and standard

* **Dependency cone of the statement.** `Ti2`, `ti2Term`, `EOddI` (project), and Mathlib's `Real.sqrt`, `tsum`,
  `Irrational`, `Odd`, `Finset` (membership in a literal `Finset ℕ`), with the ℕ → ℝ cast. Nothing else. `Ti2` does not
  depend on `chi2`. `zT`, `TT`, `c2T`, `alphaT`, `LshiftT`, `betaT`, `marginOK`, `MachineBoundsT`, `Delta`, `denT`,
  `n2T` are internal: a wrong internal definition could only make the proof fail, not weaken the statement.
* **Interface wiring** (working tree). `theoremVi : TheoremVi` (`Interface.lean` l. 283). Every ingredient is a
  one-line call to its `_proof` theorem: `padicNorm_Delta_odd_proof`, `lemmaS_proof`, `lemma10nu_proof`,
  `lemma10_0_proof`, `lemmaP_n_proof` (`Ti/NonVan.lean` l. 25), `analytic_T_proof`, `margin_Vi_proof`. The endgame
  `irrational_of_boundsT : MachineBoundsT n → Irrational (Ti2 (zT n))` (`Ti/MainCond.lean` l. 38) is proved through
  `Chi2U.irrational_of_poly_approx` (Lemma E, already audited for U).
* **Grep of `Chi2U/` and `Chi2U.lean`** (whole words `sorry`, `axiom`, `admit`, `native_decide`, `implemented_by`,
  `extern`, `unsafe`, `opaque`, `ofReduceBool`, `skipKernelTC`, `debug`, plus `run_cmd`, `#eval`, `elab`): no hits in
  the working tree, apart from the word `native_decide` in a docstring of `Cert/CertU.lean`. The only new `macro` is
  `case_close` (`Ti/Margin.lean` l. 185), a wrapper around `unfold`/`push_cast`/`linarith`. The new `instance`s are
  `fact_not_isSquare_dT` (proved) and the `ModL` field and `CharP` instances (copies of the V ones). The `set_option`s
  are linters, `maxRecDepth`, `exponentiation.threshold`, and the pre-existing `backward.isDefEq.respectTransparency`
  in the PNT port. None of these affects the kernel. Numerical checks use `decide +kernel` (339 occurrences under `Ti/`).
* **Import closure.** It is computed from `Chi2U.lean`, which at HEAD imports `Chi2U.Ti.Interface` (l. 68). It reaches
  all 130 modules under `Chi2U/`, including all 35 under `Chi2U/Ti/`. No module is orphaned.
* **Axioms** (`scripts/axioms_ti.txt`, written 10:55 by the running `lake env lean Axioms.lean`). The output is
  `'Chi2U.Ti.theoremVi' depends on axioms: [propext, Classical.choice, Quot.sound]`, and the same holds for
  `irrational_of_boundsT`, `margin_Vi`, `analytic_T`, `lemmaP_n`, `padicNorm_Delta_odd`, `lemmaS`, `lemma10nu`,
  `lemma10_0` and all 33 earlier entries (42 lines). Because `lemmaP_n` shows no `sorryAx`, the build used the working
  tree, not HEAD. `scripts/leanchecker_vi.log` had 3 lines (rc=0) when I looked, so the environment replay was still
  running.

## 3. Exception set recomputed independently: matches

Script: `scripts/ti/referee/margin_vi_referee.py` (output: `margin_vi_referee.out`). It shares no code with
`scripts/ti/margin_ti_cases.py`. It uses mpmath `iv` at 200 bits and factorises with sympy. It transcribes the formal
constants:
M(n) = 4/3 + `c2T n` + `V.cSV n` + `V.PhiL` − (log `zU 4` − log `zT n`)/2. Here `c2T` = ½ log 2 (odd n) or
|v₂(n) − 2| log 2/4 (even n), `cSV n` = Σ_{p | n odd} (v_p(n)/4 + 1/(4(p−1))) log p, Φ_L = −13538792/10⁷,
`zU 4` = √5 − 2, and `zT n` = n/2 − √((n/2)² − 1).

* For 5 ≤ n ≤ 5000, no interval contains 0. The set {n : M(n) ≥ 0} has 55 elements and is **exactly the complement
  of `marginOK`**: {6, 10, 14, 18, 30}, the odd n ≤ 69, and `EOddI`.
* With the paper's Φ_U = −1.3592162 in place of Φ_L, the set is the same. Lean's weaker Φ_L (+0.005337) costs nothing,
  because the thinnest covered cases are n = 115 (Φ_U −0.007466, Φ_L −0.002129), n = 71 (−0.007838, −0.002501),
  n = 129 (Φ_L −0.007363) and n = 73 (Φ_L −0.009778). These agree with the `Ti/Margin.lean` docstring. With Φ_U I
  reproduce the paper's Table (main.tex l. 1690ff., PROOF_TI2 §0): n = 8 −0.1624969, 12 −0.131030, 16 −0.341821,
  22 −0.015842, 197 −0.271541, 6 +0.39983, 195 +0.015625.
* **`marginOK` matches the theorem.** On [5, 5000], {n : `marginOK n`} equals {2m : m ≥ 4, m ∉ {5, 7, 9, 15}} ∪ {odd n ≥ 71,
  n ∉ EOddI}. Above 195 both sets are all n, so they are equal for every n. `theoremVi` derives `marginOK (2m)` and
  `marginOK n` from exactly the theorem's hypotheses (l. 285–301, by `omega`). `marginOK` excludes nothing the theorem
  covers, and the theorem asserts nothing that `marginOK` does not cover.
* Above 5000, Lean uses closed forms (`margin_nu2` for n ≡ 0 mod 4, `margin_nu1_large` for n ≡ 2 mod 4 and n ≥ 138,
  `margin_odd_large` for odd n ≥ 275), plus 113 cases checked one by one (28 with n ≡ 2 mod 4, 85 odd). I re-derived the
  two non-trivial bounds by hand: K − ⅛ log 276 ≈ −0.00128 and the odd n ≥ 275 bound ≈ −0.01328. Both match the
  docstring, and the count of 113 is right. The kernel checks all of this anyway.

## 4. Departures from the paper (declared, harmless)

* **Φ_L instead of Φ_U** in `betaT` (from `exists_certU'` via the shift lemma). As §3 shows, the exception set does not
  change. No direct certificates are needed, unlike V_odd's case a = 123.
* **Margins.** The paper uses a uniform P = 13 tail for n ≥ 599 plus an Arb table for n ≤ 20 000 (Prop. `marginsti`).
  Lean uses three closed-form tails (thresholds 8, 138, 275) plus 113 Lean-checked cases. It also uses a sharper bound,
  −log z_n ≥ log n − 1/(n−1)² (`log_zT_le`), instead of u_n ≥ n − 1. Only the "if" half of the Proposition is
  formalised, which is all the theorem needs.
* **Lemma P′_n.** Lean assumes ℓ ≥ 7 prime, ℓ ∤ n(n²−4), ℓ² ∤ b (`lemmaP_n`), while main.tex l. 1623 assumes only ℓ ∤ n.
  The extra condition ℓ ∤ n² − 4 (ℓ unramified) is an extra hypothesis on an internal lemma, and infinitely many ℓ remain
  (`nonvan_frequently_T`). This is the same departure as V's `lemmaP_m`.
* The paper's effective h₀ and E_an(h) are not formalised (as for U, V and V_odd), and neither are the Clausen form and
  the 57-unit corollary. None of them is part of the theorem.

## 5. Findings

### Required fixes

**R1. Commit the `Interface.lean` wiring.** HEAD `e0d271e`, titled "Theorem V_i complete in Lean … (no sorry …)",
commits only `Axioms.lean` and `Chi2U.lean`. The committed `Chi2U/Ti/Interface.lean` still has `sorry` at l. 61
(`lemmaP_n`) and lacks `import Chi2U.Ti.NonVan`. The kernel-checked, sorry-free theorem exists only in the working tree,
and the commit message is false for the committed tree. Commit the working-tree `Interface.lean` (3+/2−) together with
`scripts/axioms_ti.txt` and, once it is complete, `scripts/leanchecker_vi.log`. Rerun `#print axioms` on the committed
tree, or at least `git diff HEAD` to confirm it is empty, before tagging or pushing.

**R2. README.md.** l. 163–166 says V_i is "**not** formalised here". Replace this with a theorem-list entry
(`Chi2U.Ti.TheoremVi`, `Chi2U.Ti.theoremVi`, its axiom line) and an outline item for `Ti/` covering: the copy of the
machine with y = −z²; Lemmas 10_ν and 10_0 at trace n; Lemma P′_n with ℓ ∤ n(n²−4); Theorem B′ at `zT n` with signed
weights and the shift from `DualCertU 4`; the margins (`Ti/Margin.lean`, three closed forms plus 113 cases, generated by
`scripts/ti/margin_ti_cases.py --gen`); and the assembly. Also update the module, line and job counts (130 modules,
9178 jobs), the layout section and the thin-margin caveat (n = 115 at −0.00213, n = 71 at −0.00250 with Φ_L).

**R3. TRUST.md.**
* Axioms block (l. 3–14, "33 declarations", and the table at l. 58): now 42 entries, including `Chi2U.Ti.theoremVi`.
* Statements table (l. 68–71): add a `Chi2U/Ti/Defs.lean` row with `ti2Term`, `Ti2`, `EOddI` written out and
  `TheoremVi`, and the sentence that `summable_ti2Term` (|z| ≤ 1) and 0 < `zT n` < 1 make `Ti2` the true sum.
* Add `zT`, `c2T`, `alphaT`, `LshiftT`, `betaT`, `marginOK` to the internal constants, the case section of
  `Ti/Margin.lean` to the generated (untrusted, kernel-checked) files, and the V_i replay once `leanchecker_vi.log`
  finishes.

**R4. Paper** (`paper/main.tex`, identical to `paper_u/main.tex`). Once R1 is committed, "Theorem V_i is not formalised"
is false at l. 108, 236, 390, 1725, 2134–2135 ("nothing in the Lean project concerns the inverse tangent integral") and
2485. The Lean section should add V_i, with its statement file `Ti/Defs.lean`, and state the departures in §4: Φ_L
(no change to 𝓔_i), the closed-form tails with 113 checked cases instead of the 20 000-entry Arb table, and ℓ ∤ n(n²−4)
in Lemma P′_n. PROOF_TI2's status line ("It is not in Lean", §0 label) needs the same update.

### Suggestions (not required)

* `Ti/Interface.lean` l. 31 still says "(stubs; each is proved as `<name>_proof` in its own file)". Change "stubs" to
  the proof locations, as was done for V.
* `Ti/Defs.lean` l. 79: the `marginOK` docstring says "the exception set of the margin". It is the *complement* of the
  exception set, so say "n ≥ 5 outside the exception set".
* `lemmaP_n`'s hypothesis `¬ ℓ ∣ n * (n ^ 2 - 4)` uses truncated ℕ subtraction. This is harmless for n ≥ 3 and internal,
  but a comment would help readers.

## Checks performed

* Full read of `Ti/Defs.lean`, `Ti/Interface.lean` (working tree and HEAD), `Ti/MainCond.lean`, the header and
  reduction lemmas of `Ti/Margin.lean`, `Ti/PoleExpansion.lean` l. 25–60, `V/Defs.lean` (`oddDiv`, `cSV`, `PhiL`),
  `Field.lean` (`zU`, `zU_four`), `Defs.lean` (`chi2Term`, `abs_chi2Term_le`).
* PROOF_TI2 §0. main.tex l. 100–110, 200–236, 1547–1560, 1620–1730, 2110–2140, 2480–2490.
* Grep for unsafe constructs and options. Import closure computed in Python. `git log`, `git status`,
  `git show HEAD:Chi2U/Ti/Interface.lean`.
* Independent interval recomputation of the margins (5 ≤ n ≤ 5000) with Lean's and with the paper's Φ.
* `scripts/axioms_ti.txt` read. Not done: building, leanchecker (still running).
