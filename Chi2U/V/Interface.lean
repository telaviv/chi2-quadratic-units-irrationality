/-
# Theorem V: assembly (PROOF_V, `schanuel/four_exp/strong4/pilot_V/PROOF_V.md`)

**Theorem V.** For every `m ≥ 2`, `m ∉ E = {3, 5, 7, 9, 15}`: `χ₂(√(m² + 1) − m) ∉ ℚ` (`TheoremV`).

The machine of Theorem U is parametric in `m` (`Field`, `Moments`, `Machine`, `LemmaR`, `PoleExpansion`, `Mahler`,
`Arith/VGe`, …, all with a parameter `mz`), and so are the endgame (`MainCond.irrational_of_bounds`), the generic
odd primes `p ∤ 2m` (Lemmas 8′, 8A′, 9′: `padicNorm_Delta_odd`; Theorem A′: `theoremA`) and Theorem B′
(`DualCertU.analytic`, any `m`, given a dual certificate at `z_m`). This file states the
remaining ingredients, each proved in its own file (stage B2, 2026-11-08), and **proves** `TheoremV` (`theoremV`):

| ingredient | PROOF_V | statement (proof) |
|---|---|---|
| `lemma10nu` | §4, Lemma 10_ν | `n₂ ≤ n2V m h` (`ν = 1 + v₂(m)`) (`V/Lemma10nu`, `V/TwoAdicNu`) |
| `lemma10nu_size` | §4 ("consequently") | `n2V m h · log 2 ≤ (c₂(ν) + ε) h²` eventually — **proved** (`n2V_le`) |
| `lemmaS` | §3.2, Lemma S | odd `p ∣ m`: `n_p ≤ Σ_{l ≥ 1, p^l ≤ h} A_K(p^l) + e·(h/2 − 1)²`, `e = v_p(m)` (`V/LemmaS`, `V/S*`) |
| `AK_levels_size` | §3.2 ("for the limit") | `Σ_l A_K(p^l) ≤ (1/(4(p − 1)) + ε) h²` eventually (`V/AKSize`) |
| `shift_lemma` | §5.2 | a certificate at `z₂` gives one at `z_m` with `Φ' ≤ Φ − L(m)/2 + δ` (any `δ > 0`) (`V/Shift`) |
| `margin_V` | §0, §7 | `α(m) + Φ_L − L(m)/2 < 0` for `m ≥ 2`, `m ∉ E` (`V/Margin`) |
| `lemmaP_m` | §6, Lemma P′_m | `Δ_{3ℓ−1}(a/b) ≠ 0` for primes `ℓ ≥ 7`, `ℓ ∤ 2m(m² + 1)`, `ℓ² ∤ b` (`V/NonVan`, `NonVan/**` generic in `mz`) |

Constants (weaker than PROOF_V where the Lean pieces are weaker):
* `Φ_L = −1.3538792` (the Lean certificate: `exists_certU'`, `data.PhiQ = −1.3538792442…`) instead of PROOF_V's
  `Φ_U = −1.3592161834586374`;
* the shift lemma in the discrete certificate format of `Analytic/TheoremBU.lean` loses `L(m)/(2rL)` when every
  cell is split into `r` subcells (left-endpoint Riemann sum of `(1 − x)₊`); hence the arbitrary `δ > 0`;
* `α(m) = 4/3 + c₂(ν) + Σ_{p^e ‖ m, p odd} (e/4 + 1/(4(p − 1))) log p` exactly as in PROOF_V.
Margins with `Φ_L` (`scripts/margins_lean.py`, 60-digit arithmetic, `m ≤ 3000`, plus the closed form of PROOF_V §7
with `Φ_L`, valid for odd `m > 68` and all even `m ≥ 4`): `M(m) ≥ 0` exactly for `m ∈ E`; tightest `m = 11`
(`M = −0.012571`), `m = 21` (`−0.015023`), `m = 2` (`−0.020546`).

Proof of `theoremV` from these: denominators `denV0 m h = 2^{n2V} · Π_{p ≤ h odd, p ∤ m} p^{eOdd} ·
Π_{p ∣ m odd} p^{eS}` (integrality from `lemma10nu`, `padicNorm_Delta_odd`, `lemmaS`; size from `lemma10nu_size`,
`theoremA`, `AK_levels_size`), `β = Φ` of the shifted certificate, nonvanishing along `h = 3ℓ − 1` for large primes
`ℓ`; then `irrational_of_boundsV`.
-/
import Chi2U.V.Defs
import Chi2U.V.Lemma10nu
import Chi2U.V.Shift
import Chi2U.V.Margin
import Chi2U.V.NonVan
import Chi2U.V.LemmaS
import Chi2U.V.AKSize


namespace Chi2U
namespace V

open Polynomial Filter Finset


/-! ## The ingredients (proved in `Chi2U/V/*`) -/

/-- **Lemma 10_ν** (PROOF_V §4): `n₂(Δ_h) ≤ n2V m h` for even `h ≥ 2`. Generalises Lemma 10′ (`Arith/TwoAdic*`,
`mz = 2`, where `n₂ ≤ h⌊log₂ h⌋ + 3h`). Checked on exact `Δ_h` for `m = 1, 3, 4, 6, 8, 12`, `h ≤ 16` (`scripts/check_defs_v.py`). -/
theorem lemma10nu (m : ℕ) [Fact (1 ≤ m)] {h : ℕ} (hh : Even h) (h2 : 2 ≤ h) (k : ℕ) :
    padicNorm 2 ((Delta m h).coeff k) ≤ (2 : ℚ) ^ n2V m h := by
  exact lemma10nu_proof m hh h2 k


/-- **Lemma S** (PROOF_V §3.2): for an odd prime `p ∣ m`, `n_p ≤ Σ_{l ≥ 1, p^l ≤ h} A_K(p^l) + e(h/2 − 1)²`,
`e = v_p(m)`. Proof in `V/LemmaS.lean` (helpers `V/S*.lean`): a multi-level Lemma 8′ proved directly (Schur
complement, multilinear expansion of the bottom rows, Newton/divided-difference factorisation of `Vand(x_S)²`) plus
the polynomial-minor bound `v_p(𝒫_ij) ≥ −e(i + j − K)₊` from the Mahler form (`Mahler.Lmom_eq_mahler`,
denominators `(2m)^{b+1}`). Checked on exact `Δ_h` (`scripts/check_defs_v.py`). -/
theorem lemmaS (m : ℕ) [Fact (1 ≤ m)] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hpm : p ∣ m) {h : ℕ} (hh : Even h)
    (k : ℕ) : padicNorm p ((Delta m h).coeff k) ≤ (p : ℚ) ^ eS m h p := by
  exact lemmaS_proof m hp hpm hh k

/-- Lemma S, limit form: `Σ_l A_K(p^l) ≤ (1/(4(p − 1)) + ε) h²` eventually (`A_K(d) ≤ K²/(4d) + O(K)`,
`Σ_l p^{−l} ≤ 1/(p − 1)`). -/
theorem AK_levels_size {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    ((∑ l ∈ levelsV h p, AK h (p ^ l) : ℕ) : ℝ) ≤ (1 / (4 * ((p : ℝ) - 1)) + ε) * (h : ℝ) ^ 2 := by
  exact AK_levels_size_proof hp hp2

/-- **Shift lemma** (PROOF_V §5.2) in the certificate format of `Analytic/TheoremBU.lean`: from a certificate at
`z₂` build one at `z_m` (same `μ`, `λ' = λ − L(m)`, every cell split into `r` subcells with
`S'_{k'} = S_k − L(m)·k'/(rL)`; the tail conditions only improve since `L(m) ≥ 0`, `X ≥ 4`); then
`Φ' ≤ Φ − L(m)/2 + L(m)/(2rL)`, and `r` is taken large. -/
theorem shift_lemma (C : DualCertU 2) (m : ℕ) [Fact (1 ≤ m)] (hm : 2 ≤ m) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C' : DualCertU m, C'.Phi ≤ C.Phi - Lshift m / 2 + δ := by
  exact shift_lemma_proof C m hm hδ

/-- **The margin inequality** `M(m) < 0` (PROOF_V §0, §7) with Lean's constant `Φ_L`. Numerically: `M(m) ≥ 0`
exactly on `E` for `m ≤ 3000`; closed form beyond (`scripts/margins_lean.py`); tightest `M(11) = −0.012571`. -/
theorem margin_V {m : ℕ} (hm : 2 ≤ m) (hE : m ∉ ({3, 5, 7, 9, 15} : Finset ℕ)) :
    alphaV m + (PhiL - Lshift m / 2) < 0 := by
  exact margin_V_proof hm hE

/-- **Lemma P′_m** (PROOF_V §6) for primes `ℓ ≥ 7` with `ℓ ∤ 2m(m² + 1)` (excluding `ℓ ∣ d` avoids the ramified
and index cases; infinitely many `ℓ` remain). Proof: `V/NonVan.lean`, from Lemma P′ (`NonVan/**`), which is
generic in `mz` and needs only `ℓ ∤ 2mz` (`z`, `1 − y = 2mz·z`, `1 − z^{2ℓ}` enter only as `𝔩`-units); the
hypothesis `ℓ ∤ m² + 1` is not used. -/
theorem lemmaP_m (m : ℕ) [Fact (1 ≤ m)] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : 7 ≤ ℓ) (hℓm : ¬ ℓ ∣ 2 * m * (m ^ 2 + 1))
    (a : ℤ) {b : ℕ} (hb : 0 < b) (hb2 : ¬ ℓ ^ 2 ∣ b) : (Delta m (3 * ℓ - 1)).eval ((a : ℚ) / b) ≠ 0 := by
  exact lemmaP_m_proof m hℓ hℓm a hb hb2

/-! ## Assembly -/

/-- `|Π_{q ∈ S} q^{f q}|_p = p^{−f p}` if `p ∈ S`, else `1` (`S` a set of primes). -/
lemma padicNorm_prod_primes (p : ℕ) [Fact p.Prime] (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (f : ℕ → ℕ) :
    padicNorm p (∏ q ∈ S, (q : ℚ) ^ f q) = if p ∈ S then ((p : ℚ)⁻¹) ^ f p else 1 := by
  rw [padicNorm_prod_U]
  rw [prod_congr rfl (fun q hq => by rw [padicNorm_pow_U, padicNorm_prime_nat_U (hS q hq)])]
  rw [prod_congr rfl (fun q _ => (show (if q = p then (p : ℚ)⁻¹ else 1) ^ f q =
      if q = p then ((p : ℚ)⁻¹) ^ f p else 1 by split_ifs with he <;> simp [he]))]
  rw [prod_ite_eq']

/-- The generic odd primes `p ≤ h`, `p ∤ m`. -/
def oddGen (m h : ℕ) : Finset ℕ := (oddPrimes h).filter (fun p => ¬ p ∣ m)

lemma prime_of_mem_oddGen {m h q : ℕ} (hq : q ∈ oddGen m h) : q.Prime := (mem_filter.mp (mem_filter.mp hq).1).2.1

lemma prime_of_mem_oddDiv {m q : ℕ} (hq : q ∈ oddDiv m) : q.Prime :=
  Nat.prime_of_mem_primeFactors (mem_filter.mp hq).1

/-- The proved denominator for even `h ≥ 2`. -/
noncomputable def denV0 (m h : ℕ) : ℚ :=
  (2 : ℚ) ^ n2V m h * (∏ p ∈ oddGen m h, (p : ℚ) ^ eOdd h p) * ∏ p ∈ oddDiv m, (p : ℚ) ^ eS m h p

lemma denV0_pos (m h : ℕ) : 0 < denV0 m h := by
  unfold denV0
  refine mul_pos (mul_pos (by positivity) (prod_pos (fun p hp => ?_))) (prod_pos (fun p hp => ?_))
  · have := (prime_of_mem_oddGen hp).pos; positivity
  · have := (prime_of_mem_oddDiv hp).pos; positivity

lemma inv_pow_mul_le_one {p : ℚ} (hp : 0 < p) {e : ℕ} {x : ℚ} (hx0 : 0 ≤ x) (hx : x ≤ p ^ e) :
    (p⁻¹) ^ e * x ≤ 1 := by
  calc (p⁻¹) ^ e * x ≤ (p⁻¹) ^ e * p ^ e := mul_le_mul_of_nonneg_left hx (by positivity)
    _ = 1 := by rw [inv_pow]; field_simp

/-- `denV0 m h · Δ_h ∈ ℤ[X]` for even `h ≥ 2`. -/
theorem denV0_int (m : ℕ) [Fact (1 ≤ m)] {h : ℕ} (hh : Even h) (h2 : 2 ≤ h) (k : ℕ) :
    ∃ z : ℤ, denV0 m h * (Delta m h).coeff k = z := by
  refine exists_int_of_padicNorm_le_U _ (fun p hp => ?_)
  have := Fact.mk hp
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  unfold denV0
  rw [padicNorm.mul, padicNorm.mul, padicNorm.mul, padicNorm_pow_U, padicNorm_two_U,
    padicNorm_prod_primes p _ (fun q hq => prime_of_mem_oddGen hq),
    padicNorm_prod_primes p _ (fun q hq => prime_of_mem_oddDiv hq)]
  have hc0 := padicNorm.nonneg (p := p) ((Delta m h).coeff k)
  by_cases h2p : p = 2
  · subst h2p
    have h1 : (2 : ℕ) ∉ oddGen m h := fun hm => (mem_filter.mp (mem_filter.mp hm).1).2.2 rfl
    have h3 : (2 : ℕ) ∉ oddDiv m := fun hm => (mem_filter.mp hm).2 rfl
    rw [if_pos rfl, if_neg h1, if_neg h3, mul_one, mul_one]
    exact inv_pow_mul_le_one hp0 hc0 (by exact_mod_cast lemma10nu m hh h2 k)
  · rw [if_neg (Ne.symm h2p), one_pow, one_mul]
    by_cases hpm : p ∣ m
    · have hD : p ∈ oddDiv m := mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpm, by
        have := (Fact.out : 1 ≤ m); omega⟩, h2p⟩
      have hG : p ∉ oddGen m h := fun hm => (mem_filter.mp hm).2 hpm
      rw [if_neg hG, if_pos hD, one_mul]
      exact inv_pow_mul_le_one hp0 hc0 (lemmaS m h2p hpm hh k)
    · have hD : p ∉ oddDiv m := fun hm => hpm (Nat.dvd_of_mem_primeFactors (mem_filter.mp hm).1)
      rw [if_neg hD, mul_one]
      have hc := padicNorm_Delta_odd (p := p) h2p hpm hh k
      split_ifs with hG
      · exact inv_pow_mul_le_one hp0 hc0 hc
      · have hph : h < p := by
          by_contra hc'
          exact hG (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega), hp, h2p⟩, hpm⟩)
        rw [eOdd_eq_zero_asm hph, pow_zero] at hc
        simpa using hc

/-- The denominators used by the endgame (odd `h` and `h = 0` are not used). -/
noncomputable def denV (m : ℕ) [Fact (1 ≤ m)] (h : ℕ) : ℚ :=
  if Even h ∧ 2 ≤ h then denV0 m h else Classical.choose (exists_den (Delta m h))

lemma denV_pos (m : ℕ) [Fact (1 ≤ m)] (h : ℕ) : 0 < denV m h := by
  unfold denV
  split_ifs
  · exact denV0_pos m h
  · exact (Classical.choose_spec (exists_den (Delta m h))).1

lemma denV_int (m : ℕ) [Fact (1 ≤ m)] (h k : ℕ) : ∃ z : ℤ, denV m h * (Delta m h).coeff k = z := by
  unfold denV
  split_ifs with hh
  · exact denV0_int m hh.1 hh.2 k
  · exact (Classical.choose_spec (exists_den (Delta m h))).2 k

lemma half_sub_one_sq_le (h : ℕ) : (((h / 2 - 1) ^ 2 : ℕ) : ℝ) ≤ (h : ℝ) ^ 2 / 4 := by
  have h1 : ((h / 2 - 1 : ℕ) : ℝ) ≤ (h : ℝ) / 2 := by
    calc ((h / 2 - 1 : ℕ) : ℝ) ≤ ((h / 2 : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
      _ ≤ (h : ℝ) / 2 := Nat.cast_div_le
  push_cast
  have h0 : (0 : ℝ) ≤ ((h / 2 - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- **The arithmetic bound** at `z_m`: `log den h ≤ (α(m) + ε) h²` for even `h`, eventually. -/
theorem log_denV_le (m : ℕ) [Fact (1 ≤ m)] : ∀ ε > 0, ∀ᶠ h : ℕ in atTop, Even h →
    Real.log (denV m h) ≤ (alphaV m + ε) * (h : ℝ) ^ 2 := by
  intro ε hε
  set W : ℝ := ∑ p ∈ oddDiv m, Real.log p with hW
  have hW0 : 0 ≤ W := sum_nonneg (fun p hp => Real.log_natCast_nonneg p)
  set ε' : ℝ := ε / (3 * (W + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hS := (eventually_all_finset (oddDiv m)).2
    (fun p hp => AK_levels_size (prime_of_mem_oddDiv hp) (mem_filter.mp hp).2 ε' hε'0)
  filter_upwards [theoremA (ε / 3) (by positivity), lemma10nu_size m (ε / 3) (by positivity), hS,
    eventually_ge_atTop 2] with h hA h2 hS' hh2 hev
  have hd : denV m h = denV0 m h := by unfold denV; rw [if_pos ⟨hev, hh2⟩]
  rw [hd]
  have hne1 : ∀ p ∈ oddGen m h, ((p : ℝ)) ^ eOdd h p ≠ 0 := fun p hp =>
    pow_ne_zero _ (by exact_mod_cast (prime_of_mem_oddGen hp).ne_zero)
  have hne2 : ∀ p ∈ oddDiv m, ((p : ℝ)) ^ eS m h p ≠ 0 := fun p hp =>
    pow_ne_zero _ (by exact_mod_cast (prime_of_mem_oddDiv hp).ne_zero)
  have hlog : Real.log ((denV0 m h : ℚ) : ℝ) = (n2V m h : ℝ) * Real.log 2 +
      ∑ p ∈ oddGen m h, (eOdd h p : ℝ) * Real.log p + ∑ p ∈ oddDiv m, (eS m h p : ℝ) * Real.log p := by
    unfold denV0
    push_cast
    rw [Real.log_mul (mul_ne_zero (by positivity) (prod_ne_zero_iff.mpr hne1)) (prod_ne_zero_iff.mpr hne2),
      Real.log_mul (by positivity) (prod_ne_zero_iff.mpr hne1), Real.log_pow, Real.log_prod hne1,
      Real.log_prod hne2]
    simp only [Real.log_pow]
  rw [hlog]
  -- generic odd primes: a subset of the odd primes `≤ h`
  have hG : ∑ p ∈ oddGen m h, (eOdd h p : ℝ) * Real.log p ≤ (4 / 3 + ε / 3) * (h : ℝ) ^ 2 :=
    le_trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p))) hA
  -- special primes
  have hSp : ∑ p ∈ oddDiv m, (eS m h p : ℝ) * Real.log p ≤ (cSV m + ε / 3) * (h : ℝ) ^ 2 := by
    have hterm : ∀ p ∈ oddDiv m, (eS m h p : ℝ) * Real.log p ≤
        ((padicValNat p m : ℝ) / 4 + 1 / (4 * ((p : ℝ) - 1))) * Real.log p * (h : ℝ) ^ 2 +
          ε' * Real.log p * (h : ℝ) ^ 2 := by
      intro p hp
      have hlp := Real.log_natCast_nonneg p
      have h1 := hS' p hp
      have h2 := half_sub_one_sq_le h
      have he : (eS m h p : ℝ) ≤ (1 / (4 * ((p : ℝ) - 1)) + ε') * (h : ℝ) ^ 2 +
          (padicValNat p m : ℝ) * ((h : ℝ) ^ 2 / 4) := by
        unfold eS
        push_cast
        have h1' : ((∑ l ∈ levelsV h p, AK h (p ^ l) : ℕ) : ℝ) = ∑ l ∈ levelsV h p, (AK h (p ^ l) : ℝ) := by
          push_cast; rfl
        rw [h1'] at h1
        have h2' : ((h / 2 - 1 : ℕ) : ℝ) ^ 2 ≤ (h : ℝ) ^ 2 / 4 := by exact_mod_cast h2
        have hv : (0 : ℝ) ≤ padicValNat p m := Nat.cast_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left h2' hv]
      have := mul_le_mul_of_nonneg_right he hlp
      nlinarith
    calc ∑ p ∈ oddDiv m, (eS m h p : ℝ) * Real.log p
        ≤ ∑ p ∈ oddDiv m, (((padicValNat p m : ℝ) / 4 + 1 / (4 * ((p : ℝ) - 1))) * Real.log p * (h : ℝ) ^ 2 +
          ε' * Real.log p * (h : ℝ) ^ 2) := sum_le_sum hterm
      _ = cSV m * (h : ℝ) ^ 2 + ε' * W * (h : ℝ) ^ 2 := by
          simp only [cSV, hW, sum_add_distrib, sum_mul, mul_sum]
      _ ≤ (cSV m + ε / 3) * (h : ℝ) ^ 2 := by
          have : ε' * W ≤ ε / 3 := by
            rw [hε', div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
          nlinarith [sq_nonneg (h : ℝ)]
  unfold alphaV
  nlinarith [sq_nonneg (h : ℝ)]

/-- Infinitely many even `h` with `Δ_h(a/b) ≠ 0` (Lemma P′_m along `h = 3ℓ − 1`, `ℓ` a large prime). -/
theorem nonvan_frequently_V (m : ℕ) [Fact (1 ≤ m)] (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ∃ᶠ h : ℕ in atTop, Even h ∧ (Delta m h).eval ((a : ℚ) / b) ≠ 0 := by
  rw [frequently_atTop]
  intro N
  obtain ⟨ℓ, hℓN, hℓp⟩ := Nat.exists_infinite_primes (N + b + 7 + 2 * m * (m ^ 2 + 1))
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have hℓ7 : 7 ≤ ℓ := by omega
  have hodd : Odd ℓ := hℓp.odd_of_ne_two (by omega)
  have hpos : 0 < 2 * m * (m ^ 2 + 1) := by have := (Fact.out : 1 ≤ m); positivity
  refine ⟨3 * ℓ - 1, by omega, ?_, lemmaP_m m hℓ7 (fun hd => ?_) a hb ?_⟩
  · obtain ⟨k, rfl⟩ := hodd
    exact ⟨3 * k + 1, by omega⟩
  · have := Nat.le_of_dvd hpos hd; omega
  · intro hdvd
    have hle := Nat.le_of_dvd hb hdvd
    have : ℓ ≤ ℓ ^ 2 := Nat.le_self_pow (by norm_num) ℓ
    omega

/-- The endgame inputs at `z_m`. -/
theorem exists_boundsV {m : ℕ} [Fact (1 ≤ m)] (hm : 2 ≤ m) (hE : m ∉ ({3, 5, 7, 9, 15} : Finset ℕ)) :
    Nonempty (MachineBoundsV m) := by
  obtain ⟨C, hC⟩ := exists_certU'
  have hM := margin_V hm hE
  set M : ℝ := alphaV m + (PhiL - Lshift m / 2) with hMdef
  obtain ⟨C', hC'⟩ := shift_lemma C m hm (δ := -M / 2) (by linarith)
  have hCL : C.Phi < PhiL := by rw [PhiL]; exact hC
  exact ⟨{
    den := denV m
    den_pos := denV_pos m
    den_int := denV_int m
    α := alphaV m
    β := C'.Phi
    margin := by linarith
    arith := log_denV_le m
    analytic := C'.analytic
    nonvan := nonvan_frequently_V m }⟩

/-- **Theorem V.** -/
theorem theoremV : TheoremV := by
  intro m hm hE
  have : Fact (1 ≤ m) := ⟨by omega⟩
  obtain ⟨H⟩ := exists_boundsV hm hE
  exact irrational_of_boundsV H

end V
end Chi2U
