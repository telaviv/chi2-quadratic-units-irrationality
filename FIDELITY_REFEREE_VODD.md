# Fidelity referee report: Theorem V_odd (`Chi2U.VOdd.theoremVOdd`)

Referee: independent AI fidelity referee (Claude), 2026-11-08. Branch `theorem-vodd`, HEAD `619a75d` plus the
uncommitted wiring in the working tree (`Chi2U.lean` imports `Cert.Lin`, `Cert.LinInstance`, `Cert.LogTab`,
`VOdd.Interface`; `VOdd/Interface.lean` replaces the three `sorry` stubs by `lemma10_0_proof`, `exists_certOdd_proof`,
`margin_VOdd_proof`; `Axioms.lean` adds five `#print axioms` lines). Read-only review: I did not build, so I have **not**
seen the `#print axioms` output for `theoremVOdd` (the build and `scripts/leanchecker_vodd.log` were in progress and
the log was empty). Scope: what is new since Theorem V (`FIDELITY_REFEREE_V.md`); V's ingredients were not re-checked.

**Verdict: PASS WITH FIXES.** The Lean statement is the paper's Theorem 1.3 (V_odd) exactly; the trusted base is
unchanged; the new certificate pipeline is sound as stated, and the statements used downstream are the right ones.
The required fixes are documentation only (README, TRUST, and the paper's Lean section, which now say false things
about the code). They are conditional on the running build printing `[propext, Classical.choice, Quot.sound]` for
`Chi2U.VOdd.theoremVOdd`.

---

## 1. Statement fidelity: faithful

`Chi2U/VOdd/Defs.lean`:

```lean
def TheoremVOdd : Prop :=
  ∀ a : ℕ, Odd a → 5 ≤ a → a ∉ EOdd → Irrational (chi2 ((Real.sqrt ((a : ℝ) ^ 2 + 4) - a) / 2))
```

* **Function.** `chi2 z = ∑' n, z^(2n+1)/(2n+1)²` (`Chi2U/Defs.lean`, unchanged since U). This is the paper's
  χ₂(q) = Σ_{n≥0} q^{2n+1}/(2n+1)² (main.tex l. 123). The point (√(a²+4) − a)/2 lies in (0, 1/a) ⊂ (0, 1), so the
  `tsum` is the true sum (`summable_chi2Term` for |z| ≤ 1).
* **Point.** It is literally the paper's α_a = (√(a²+4) − a)/2 (main.tex l. 175, 187). The statement does not go
  through `zU`. `zU_eq_half` (`zU a = (√(a²+4) − a)/2`, with `zU az := √((az/2)² + 1) − az/2`) is proved, not
  assumed. It is used only in the last line of `theoremVOdd` to rewrite `TU a = chi2 (zU a)` into the stated form.
* **Range.** `a : ℕ`, `Odd a`, `5 ≤ a`: these are the paper's "odd integer a ≥ 5". There are no extra hypotheses, and
  the `Fact (1 ≤ a)` instance is built inside the proof.
* **Exception set.** Lean's `EOdd` is {5, 7, …, 57} (27 values, all listed) ∪ {63, 65, 69, 75, 77, 81, 85, 87, 93, 99,
  105, 165}, 39 values in all. I compared it element by element with the paper's
  𝓔_odd = {5, 7, 9, …, 57} ∪ {63, 65, 69, 75, 77, 81, 85, 87, 93, 99, 105, 165} (main.tex l. 183) and with
  PROOF_VODD §0: they are identical.
* **Vacuity or triviality.** None. `Irrational` is Mathlib's. `EOdd` is a concrete `Finset ℕ`, and infinitely many
  odd a satisfy the hypotheses.

I also recomputed the exception set myself (mpmath, 40 digits, odd a ≤ 6001, with alphaO and betaO transcribed from
Lean). The set {a : M(a) ≥ 0} is exactly `EOdd`, both with Lean's constants (Φ_L, the 11 `PhiC`) and with the paper's
(Φ_U, the 10 Table 6 values). Lean's thinnest margins: a = 135 (cert) −0.000249, a = 59 (cert) −0.00139, a = 115
(shift) −0.00217 after Lean's relaxation of L(a). These match the `Margin.lean` docstring.

## 2. Trusted base: unchanged and standard

* The statement depends only on `chi2`/`chi2Term` (`Defs.lean`), `EOdd`, Mathlib's `Real.sqrt`, `Irrational`, `Odd`
  and `Finset`. Everything else (`zU`, `alphaO`, `betaO`, `PhiC`, `certA`, `n2O`, `DualCertU`, `LinCertU`, `CDataLin`)
  is internal: a wrong internal definition could only make the proof fail, not make the statement weaker.
* Grep of `Chi2U/` and `Chi2U.lean` for `sorry`, `axiom`, `native_decide`, `implemented_by`, `@[extern]`, `unsafe`,
  `opaque`, `ofReduceBool`, `run_cmd`, `#eval`, `elab`: no hits. The one match is the word `native_decide` inside a
  docstring of `Cert/CertU.lean`. The `macro`s are `bsmall_close` (V) and `case_close` (`VOdd/Margin.lean`), both plain
  wrappers around `unfold`/`push_cast`/`linarith`. All numerical checks use `decide +kernel`. The new `instance`
  declarations are the pre-existing `Fact` instances of `Field.lean`, all proved.
* **Imports.** I computed the import closure of `Chi2U.lean` in the working tree: every one of the 95 modules under
  `Chi2U/` is reached, including `VOdd/{Defs,TenZero,Margin,CertOdd,Interface}`, the 11 `VOdd/CertData/A*.lean` (via
  `CertOdd`), and `Cert/{Lin,LinInstance,LogTab}`. Note that **at HEAD (`619a75d`) `Chi2U.lean` does not import
  `VOdd.Interface`, and `Interface.lean` still has three `sorry`s**. The uncommitted working-tree changes must be
  committed together; until then the committed branch does not contain the theorem.
* `Axioms.lean` (working tree) lists `theoremVOdd`, `lemma10_0`, `exists_certOdd`, `margin_VOdd` and `exists_certU`.
  I have not seen its output.

## 3. The new certificate format: sound as stated

* **`LinCertU` → `DualCertU`** (`Cert/Lin.lean`). The `LinCertU az` structure has the same μ, λ, X and tail fields as
  `DualCertU az`, with the same `zU az` in `htail1`/`htail2`. `hF` is a per-cell affine majorant of `2U^μ + vU az`.
  `refine r` builds a genuine `DualCertU az`, at the same `az`, with grid `L·r` and cell bound `Sref` (the larger
  endpoint value of the affine majorant on each subcell). `exists_dual : ∃ D : DualCertU az, D.Phi ≤ C.PhiLin + δ`.
  The trapezoid charge is the correct convex bound. Theorem B′ (`DualCertU.analytic`) is applied to the refined
  `DualCertU` without change, so no analytic statement changed.
* **Checked data → `LinCertU`** (`Cert/LinInstance.lean`). `CDataLin` carries `az`. `Valid` checks
  `(2 zlo + az)² ≤ az² + 4 ≤ (2 zhi + az)²` with `0 < zlo` and `0 ≤ 2 zhi + az`. `zlo_le_az` and `le_zhi_az` turn these
  into `zlo ≤ zU az ≤ zhi`, so **the z-enclosure is for `zU d.az`**. The log z enclosure (`mem_lw`) is for
  `Real.log (zU d.az)`, and `F_eq` rewrites `2U^μ + vU d.az` with that same `log (zU d.az)`.
  `exists_dual_le : ∃ C : DualCertU d.az, C.Phi ≤ t` for rational `t > PhiQ`.
* **The 11 instances** (`VOdd/CertData/A*.lean`). Each `data` has `az := 59, 61, 67, 91, 95, 111, 117, 123, 135, 147,
  195`, matching its file name. Each `cert : ∃ C : DualCertU a, C.Phi ≤ (PhiC a : ℚ)` comes from
  `exists_dual_le valid phiQ_lt`, where `phiQ_lt : data.PhiQ < PhiC a` is checked by `decide +kernel`, so `d.az ≡ a`
  holds definitionally. `exists_certOdd_proof` splits on `a ∈ certA` with `rfl` and uses each `cert`. So
  **`exists_certOdd` really gives a `DualCertU a` at the trace a.** The differing `Fact (1 ≤ a)` proofs are
  proof-irrelevant.
* **Theorem U's certificate moved to the new format** (`Cert/DataU.lean`, `az := 4`, grid 1/40, 160 cells, 4 chunks,
  `PhiQ = −27083980489111/20000000000000 ≈ −1.3541990 < −677/500`). The statements
  `exists_certU' : ∃ C : DualCertU 4, C.Phi < -13538792 / 10000000` and
  `exists_certU : ∃ C : DualCertU 4, C.Phi < -27 / 20` are **character-for-character unchanged** from `bf3f972`; only
  the proofs changed. `Core.lean` (the cell sums and the log table check) is unchanged. `Cert/Instance.lean` (the old
  `CDataU`) is still built and supplies the shared lemmas, but no longer carries any certificate.
* **The log table** (`Cert/LogTab.lean`, 1004 entries, `tabOK` by `decide +kernel` against `checkTab`) is untrusted
  data checked by the kernel.

## 4. Departures from the paper

* **Lemma 10_0** (`VOdd/TenZero.lean`). The Lean statement `padicNorm 2 ((Delta az h).coeff k) ≤ 2 ^ (h²/2 + h)`
  (odd `az`, even `h ≥ 2`) is the paper's "n₂ ≤ h²/2 + h for every even h" (main.tex l. 1419). The entry bounds are
  the paper's (L) and (U). The (U′) form `v₂ ≥ 2 − v₂(N₀!)` equals the paper's 2 − N₀ + s₂(N₀) and is then weakened
  to 2 − N₀ = g(s), which is all the tent minorant needs. The Karamata step is replaced by concavity
  (g(2i) + g(2j) ≤ 2g(i+j)) and a weighted Leibniz bound with integer weights ⌊g(2i)/2⌋, ⌈g(2j)/2⌉. Since h is even,
  every g(2i) is even, so no rounding is lost, and the total is Σ g(2i) = 2h − h²/2, as in the paper. This is a
  faithful, declared departure, the same as for Lemma 10_ν.
* **Margins** (`VOdd/Margin.lean`). The paper (Prop. 8.2) uses a closed form for a > e^{8C₀} ≈ 4188 and an Arb table
  for a ≤ 5001. Lean instead splits off p = 3, 5, 7 to get a closed form for a ≥ 275. I re-derived it:
  cSV − ½ log a = −(9/40) log a + Σ (1/(4(p−1)) − e/40) log p, with each term ≤ 0 for p ≥ 11 and ≤ 1/10, 3/80, 1/60
  times log p for p = 3, 5, 7. The resulting bound at a = 275 is −0.01328. The 96 odd a < 275 outside `EOdd` are
  checked one by one (`finL`, completeness `finL_mem` by `decide +kernel`). Off `certA`, Lean relaxes
  L(a) > log a − log(√5+2); the worst relaxed case is a = 115 at −0.00217. This is sound, and it covers the paper's
  range.
* **Constants.**
  * `alphaO a = 4/3 + ½ log 2 + cSV a`, with `cSV a = Σ_{p ∈ oddDiv a} (v_p(a)/4 + 1/(4(p−1))) log p`. This is the
    paper's 4/3 + c₂(0) + Σ_{p^e‖a} c_p(e), with c₂(0) = ½ log 2 and c_p(e) = (e/4 + 1/(4(p−1))) log p
    (main.tex l. 724, eq. (Modd)). For odd a, `oddDiv a` is all of a's prime factors.
  * `betaO` is `PhiC a` on `certA`, else `Φ_L − LshiftA a / 2` with `LshiftA a = log zU 4 − log zU a`, which is the
    paper's L(a) = log((√5−2)/α_a).
  * The 4/3 comes from `theoremA` and the ½ log 2 from `lemma10_0_size`. In `log_denO_le`, the special-prime term
    (`AK_levels_size` plus `v_p(a)(h/2−1)² ≤ v_p(a) h²/4`) gives exactly `cSV`.
* **What Lean uses that the paper does not:**
  * Φ_L = −1.3538792 instead of Φ_U = −1.3592162. That is 0.00534 weaker, so **a = 123** (paper: −0.000034 with the
    shift lemma alone) has shift margin +0.0053 in Lean and needs a direct certificate. Lean therefore has 11 direct
    certificates, not 10.
  * Lean's 11 certificates are its own coarse linear-majorant certificates (grids L = 20…100), not the paper's
    N = 1600 Arb certificates. Their `PhiC` values are 0.0005 to 0.015 above Table 6 (for example a = 59: −2.71826
    vs −2.73026), so Lean's certified margins are thinner (a = 135: −0.00025 vs −0.00089).
  * Nonvanishing uses `lemmaP_m` with ℓ ≥ 7, ℓ ∤ a(a²+4), along h = 3ℓ − 1, rather than the paper's 𝓗 (ℓ ≥ 37,
    ℓ ∤ a). This is harmless: infinitely many ℓ remain, and the V section of the paper already describes this
    instance.
  * None of these changes the theorem. The paper should state them once V_odd is described as formalised (see fix R3).
* **What the paper claims that Lean does not cover:** only the "only if" half of Prop. 8.2 (that M_odd ≥ 0 on
  𝓔_odd), which is not part of the theorem. The paper's E_an(h) and effective h₀ are not formalised, as for V.

## 5. Documentation

### Required fixes

**R1. README.md** (it currently describes V_odd as not formalised, and the Theorem U certificate wrongly):
* Add Theorem V_odd to the theorem list and to the Lean snippet (`Chi2U.VOdd.TheoremVOdd`, `theoremVOdd`), and its
  axiom line. Consider the norm −1 corollary wording: the even and odd theorems together give all norm −1 units
  except the 47. Note that the corollary itself is not a Lean statement.
* Delete or rewrite the paragraph "The paper also proves two extensions that are **not** formalised here…": V_odd is
  now formalised, Ti₂ (V_i) is not.
* Outline item 3: the certificate is now in the linear-majorant format, grid 1/40 (160 cells), Φ_Q ≈ −1.3541990
  (≤ −1.354), refined to a `DualCertU` by `LinCertU.exists_dual`. "Φ ≤ −1.3538792" is no longer the certificate's
  value; it is the constant Φ_L.
* Add an outline item for V_odd: Lemma 10_0 (`VOdd/TenZero`), the 11 direct certificates (`VOdd/CertOdd`,
  `VOdd/CertData/`, why a = 123 is included), the margins (`VOdd/Margin`, closed form a ≥ 275, 96 cases), and the
  assembly (`VOdd/Interface`).
* "Building and checking": the regeneration command `python scripts/gen_cert_u.py 50 8 4 Chi2U/Cert/DataU.lean` is
  wrong. It is now `python scripts/gen_cert_u.py` (no arguments; it calls `gen_cert_lin.py 4 10 8 4 … --chunk 40` and
  also writes `Cert/LogTab.lean`). Add `gen_cert_lin.py` (the V_odd certificate data) and `margin_vodd_cases.py` (the
  generated case section of `VOdd/Margin.lean`, plus the 60-digit margin recomputation).
* Repository layout: add `VOdd/`, `Cert/Lin.lean`, `Cert/LinInstance.lean`, `Cert/LogTab.lean`, the new scripts,
  `FIDELITY_REFEREE_VODD.md`, and `scripts/leanchecker_vodd.log` once it is filled.
* Update the job count (9124), the line counts (now about 23,300 lines in 95 modules), and the "thin margins" caveat
  (add a = 135 at −0.00025 and a = 59 at −0.0014).

**R2. TRUST.md:**
* The Axioms block: add `Chi2U.VOdd.theoremVOdd` once printed.
* The bullet "proved by `decide +kernel` (`Cert/CertU.lean`, 16 chunks of grid cells, a log table of 2004 entries …)"
  is **false** now. It should say: `Cert/DataU.lean`, 4 chunks of 40 cells, the 1004-entry table in
  `Cert/LogTab.lean`, plus the 11 V_odd certificates in `VOdd/CertData/` and the margin cases in `VOdd/Margin.lean`
  (`decide +kernel` for `logPt` enclosures and `finL_mem`).
* "Environment replay": add the V_odd replay (95 modules) when `leanchecker_vodd.log` is complete.
* "Fresh-clone check": state that it predates V_odd.
* "The statements" table: add the `Chi2U/VOdd/Defs.lean` row (`TheoremVOdd`, `EOdd` written out) and the sentence
  that 0 < (√(a²+4) − a)/2 < 1, so `chi2` is the true sum. Add `alphaO`, `betaO`, `PhiC`, `certA` to the list of
  internal constants.
* "Generated files": the command is stale (as in R1). Add `Cert/LogTab.lean`, `VOdd/CertData/*.lean`
  (`gen_cert_lin.py`) and the case section of `VOdd/Margin.lean` (`margin_vodd_cases.py --gen`) as untrusted,
  kernel-checked inputs.
* "Who checked what": add the PROOF_VODD gate referee (REFEREE_VODD) and this report.

**R3. Paper** (`paper/main.tex`, identical to `paper_u/main.tex`). Its Lean description is now false in two ways:
* Since `e2127b1`, the Theorem U certificate is no longer "50 cells … L = 200 … Φ_Q = −54155169767979/4·10¹³"
  (l. 2219–2225). The generator command (l. 2257–2258) and "16 chunks … 2004 logarithm enclosures" (l. 2260) are also
  stale; the new format is a linear majorant per cell with trapezoid charge, plus grid refinement.
* Once V_odd is merged, "not formalised" at l. 105–110, 232, 384, 1717 and 2123–2126 is false. In particular, "nothing
  in the Lean project concerns odd a" (l. 2125) is already false since the C0 re-parametrisation.

The Lean section should then add an item for V_odd giving:
* Lemma 10_0 via the weighted Leibniz bound;
* Φ_L in place of Φ_U, which makes **a = 123 need a direct certificate in Lean** (11 certificates, against the paper's
  10). The paper should say this, because l. 1513 presents 123 as shift-only;
* Lean's own coarser certificates, with values above Table 6 and thinnest margin a = 135 at about −0.00025;
* the margin closed form for a ≥ 275 plus 96 Lean-checked cases.

### Suggestions (not required)

* `V/Defs.lean`: the docstring of `PhiL` ("the exponent of Theorem U's Lean certificate") is now only an upper bound.
  The current certificate gives ≤ −1.354. Reword it as "a rounded bound proved by `exists_certU'`". The same applies
  to the "Constants" line of `VOdd/Interface.lean`.
* `VOdd/Interface.lean`: the ingredient table still has the stub-era layout (only `lemma10_0_size` is marked
  "proved"). Name the proof locations (`TenZero.lemma10_0_proof`, `CertOdd.exists_certOdd_proof`,
  `Margin.margin_VOdd_proof`), as was done for V after its referee.
* Commit the working-tree wiring (`Chi2U.lean`, `Interface.lean`, `Axioms.lean`) in one commit, so that no committed
  state imports V_odd with `sorry`s and none leaves it unimported.
* README title ("… for every m ≥ 16") predates V and V_odd and should be refreshed with R1.
* Optional slack: `exists_certU'` could be restated at −677/500 (= −1.354), which the new certificate already
  proves. That gains only 1.2·10⁻⁴ in the margins and would not remove a = 123 (it needs 0.0053), so it is not worth
  touching V's statements.

## Checks performed

* `git diff bf3f972 HEAD`, `git diff HEAD` (working tree), `git show bf3f972:Chi2U/Cert/CertU.lean` (statements of
  `exists_certU`, `exists_certU'`).
* Full read of `VOdd/Defs`, `VOdd/Interface`, `VOdd/CertOdd`, `Cert/Lin`, `Cert/LinInstance`, `Cert/CertU`,
  `Cert/DataU`; the docstrings and statements of `VOdd/TenZero` and `VOdd/Margin` (large-a lemma read in full); the
  headers and `cert` statements of all 11 `VOdd/CertData/A*.lean`; `MainCond.MachineBounds`; the V ingredient
  signatures (`lemmaS`, `AK_levels_size`, `shift_lemma`, `lemmaP_m`).
* Grep for unsafe constructs; computation of the import closure (Python).
* Independent margin recomputation (mpmath, 40 digits, odd a ≤ 6001) with Lean's and with the paper's constants;
  Lean's relaxed shift bound on a < 275; the closed form at a = 275.
* Paper main.tex l. 170–200, 1386–1530, 2110–2262; PROOF_VODD §0, §4.
* Not done: building, `#print axioms`, leanchecker (left to the running process).
