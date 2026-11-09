/-
# Theorem V_i: odd primes `p ∤ n`, the row claim and Lemma 9′ (PROOF_TI2 §2 row "§3.1 generic odd p ∤ n")

**Copy of `Chi2U/Arith/OddPrimes.lean`** for the Ti₂ machine. PROOF_TI2 §2: PROOF_V §3.1 holds verbatim with
`y = −z²`, `1 − y = n z`; for an odd prime `p ∤ n` (ramified `p ∣ n² − 4` included: `gcd(n, n² − 4) ∣ 4`) the numbers
`z`, `y`, `1 − y` are `p`-units. The `z`-free parts are reused from `Chi2U.L9` (`Fpoly`, `divByMonic_offdiag`,
`divByMonic_diag`, `cPole_ff`, the level counting of `Lemma9Levels.lean`: `prod_T_le`, `prod_DD_le`, `deriv_Fpoly_le`,
`deriv_DD_le`, `padicValRat_dPrime`, `Vexp_le_factorial`).

Changes against the χ₂ file (the proof is the same):
* the pole factor is `(−1)^{x/2} z^x` (`sgnPole`), a `p`-unit (`vGe_sgnPole`);
* the partial sums carry the signs `χ₄(u) = (−1)^k` (units) and have no overall minus for `x > 0` (`vGe_Psum`);
* `vGe_Lmom_odd` is the Ti₂ Mahler form (denominators `n^{b+1}`, `Ti/Mahler.lean`).
-/
import Chi2U.Ti.LemmaB

set_option linter.unusedSectionVars false

namespace Chi2U
namespace Ti

variable {n : ℕ} [Fact (3 ≤ n)]

open Polynomial Finset

variable {h p : ℕ}

/-- The sign `(−1)^{x/2}` of a pole factor is a `p`-unit. -/
lemma vGe_sgnPole [Fact p.Prime] (x : ℤ) : vGe p 0 (((sgnPole x : ℚ)) : Qt n) := by
  refine vGe_ratCast_of_padicNorm ?_
  unfold sgnPole
  have := padicNorm.of_int (p := p) ((-1 : ℤ) ^ (x / 2).natAbs)
  push_cast at this
  simp

/-- `(−1)^k ∈ O_p`. -/
lemma vGe_neg_one_pow [Fact p.Prime] (k : ℕ) : vGe p 0 ((-1 : Qt n) ^ k) :=
  vGe_of_pInt (pInt_pow (pInt_neg pInt_one) k)

namespace L9

open _root_.Chi2U.L9

/-! ### Pole coefficients -/

lemma sum_cPole_ff {h i : ℕ} (j : ℕ) (hi : i ≤ h) (F : ℕ → (Qt n)) :
    ∑ m ∈ range (h + 1), (cPole h (fLag h i * fLag h j) m : (Qt n)) * F m =
      if i = j then (dPrime h i : (Qt n)) * F i else 0 := by
  rw [sum_eq_single i]
  · rw [cPole_ff i j hi]
    by_cases hij : i = j
    · rw [if_pos ⟨rfl, hij⟩, if_pos hij]
    · rw [if_neg (fun hh => hij hh.2), if_neg hij]; simp
  · intro m hm hmi
    rw [cPole_ff i j (Nat.lt_succ_iff.mp (mem_range.mp hm)), if_neg (fun hh => hmi hh.1)]
    simp
  · intro hh; exact absurd (mem_range.mpr (Nat.lt_succ_of_le hi)) hh

lemma Bfun_ff {h i : ℕ} (j : ℕ) (hi : i ≤ h) :
    Bfun n h (fLag h i * fLag h j) = if i = j then
      -((dPrime h i : (Qt n)) * (sgnPole (poleZ h i) : (Qt n)) * (zK n) ^ (poleZ h i)) else 0 := by
  have := sum_cPole_ff j hi (fun m => (sgnPole (poleZ h m) : (Qt n)) * (zK n) ^ (poleZ h m))
  simp only [← mul_assoc] at this
  unfold Bfun
  rw [this]
  split_ifs <;> simp

lemma Afun_ff {h i : ℕ} (j : ℕ) (hi : i ≤ h) :
    Afun n h (fLag h i * fLag h j) = muPoly n ((fLag h i * fLag h j) /ₘ Dpoly h) +
      if i = j then (dPrime h i : (Qt n)) * (sgnPole (poleZ h i) : (Qt n)) * (zK n) ^ (poleZ h i) *
        Psum n (poleZ h i) else 0 := by
  have := sum_cPole_ff j hi
    (fun m => (sgnPole (poleZ h m) : (Qt n)) * (zK n) ^ (poleZ h m) * Psum n (poleZ h m))
  simp only [← mul_assoc] at this
  unfold Afun
  rw [this]

/-! ### Valuations -/

variable [hp : Fact p.Prime]

lemma vGeX_zero' (v : ℤ) : vGeX p v (0 : (Qt n)[X]) := fun k => by rw [coeff_zero]; exact vGe_zero v

lemma vGeX_mono' {v w : ℤ} (hmn : w ≤ v) {F : (Qt n)[X]} (hF : vGeX p v F) : vGeX p w F :=
  fun k => vGe_mono hmn (hF k)

/-- `v_p(P(x)) ≥ −2 lev*(p)` for `|x| ≤ h`. -/
lemma vGe_Psum {x : ℤ} (hx : x.natAbs ≤ h) : vGe p (-(2 * (levU h p : ℤ))) (Psum n x) := by
  have hterm : ∀ k ∈ range (x.natAbs / 2),
      padicNorm p ((1 : ℚ) / ((2 * (k : ℚ) + 1) * (2 * k + 1))) ≤ (p : ℚ) ^ (-(-(2 * (levU h p : ℤ)))) := by
    intro k hk
    rw [mem_range] at hk
    have e : (2 * (k : ℚ) + 1) = ((2 * (k : ℤ) + 1 : ℤ) : ℚ) := by push_cast; ring
    have hν := nuL_le (p := p) h (2 * (k : ℤ) + 1)
    rw [e, padicNorm.div, padicNorm.one, padicNorm.mul, padicNorm_int_eq (h := h) (by omega) (by omega),
      neg_neg, ← pow_add, one_div, inv_pow, inv_inv, ← zpow_natCast]
    exact zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_lt.le) (by push_cast; omega)
  unfold Psum
  split_ifs
  · refine vGe_sum _ _ (fun k hk => ?_)
    rw [show (-1 : Qt n) ^ k * (zK n) ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : (Qt n)) ^ 2 =
        (-1) ^ k * ((zK n) ^ ((2 * k + 1 : ℕ) : ℤ) *
          (((1 : ℚ) / ((2 * (k : ℚ) + 1) * (2 * k + 1)) : ℚ) : (Qt n))) by rw [zpow_natCast]; push_cast; ring]
    have := vGe_mul (vGe_neg_one_pow (n := n) (p := p) k)
      (vGe_mul (vGe_zK_zpow (n := n) (p := p) ((2 * k + 1 : ℕ) : ℤ)) (vGe_ratCast_of_padicNorm (hterm k hk)))
    simpa using this
  · refine vGe_sum _ _ (fun k hk => ?_)
    rw [show (-1 : Qt n) ^ k * ((zK n) ^ (2 * k + 1))⁻¹ / ((2 * k + 1 : ℕ) : (Qt n)) ^ 2 =
        (-1) ^ k * ((zK n) ^ (-((2 * k + 1 : ℕ) : ℤ)) *
          (((1 : ℚ) / ((2 * (k : ℚ) + 1) * (2 * k + 1)) : ℚ) : (Qt n))) by
        rw [zpow_neg, zpow_natCast]; push_cast; ring]
    have := vGe_mul (vGe_neg_one_pow (n := n) (p := p) k)
      (vGe_mul (vGe_zK_zpow (n := n) (p := p) (-((2 * k + 1 : ℕ) : ℤ))) (vGe_ratCast_of_padicNorm (hterm k hk)))
    simpa using this

end L9

open _root_.Chi2U.L9

/-- **Row claim** of Lemma 9′ (both the `A` and the `B` part of `G^f_{ij}`); Ti₂ version of `Chi2U.rowClaim`. -/
theorem rowClaim [Fact p.Prime] (hp : p ≠ 2) (hpm : ¬ p ∣ n) (hh : Even h) {i j : ℕ} (hi : i ≤ h) (hj : j ≤ h) :
    vGe p (padicValRat p (dPrime h i) - 2 * levU h p) (Afun n h (fLag h i * fLag h j)) ∧
      vGe p (padicValRat p (dPrime h i) - 2 * levU h p) (Bfun n h (fLag h i * fLag h j)) := by
  have hmu : vGe p (padicValRat p (dPrime h i) - 2 * levU h p) (muPoly n ((fLag h i * fLag h j) /ₘ Dpoly h)) := by
    refine vGe_Lmom_odd hpm _ _ (fun k => ?_)
    rw [zpow_bound]
    by_cases hij : i = j
    · subst hij; rw [divByMonic_diag hi]; exact deriv_DD_le hp hi k
    · rw [divByMonic_offdiag hi hj hij]; exact deriv_Fpoly_le hp hi j k
  have hD : vGe p (padicValRat p (dPrime h i))
      ((dPrime h i : (Qt n)) * (sgnPole (poleZ h i) : (Qt n)) * (zK n) ^ poleZ h i) := by
    have := vGe_mul (vGe_mul (vGe_ratCast (n := n) (p := p) (dPrime h i)) (vGe_sgnPole (poleZ h i)))
      (vGe_zK_zpow (n := n) (p := p) (poleZ h i))
    rwa [add_zero, add_zero] at this
  constructor
  · rw [Ti.L9.Afun_ff j hi]
    refine vGe_add hmu ?_
    split_ifs
    · have := vGe_mul hD (Ti.L9.vGe_Psum (n := n) (p := p) (natAbs_poleZ_le hh hi))
      convert this using 2
      ring
    · exact vGe_zero _
  · rw [Ti.L9.Bfun_ff j hi]
    split_ifs
    · exact vGe_mono (by have := (levU h p).cast_nonneg (α := ℤ); linarith) (vGe_neg hD)
    · exact vGe_zero _

/-- **Lemma 9′** (plateau bound); Ti₂ version of `Chi2U.lemma9`. -/
theorem lemma9 [Fact p.Prime] (hp : p ≠ 2) (hpm : ¬ p ∣ n) (hh : Even h) (k : ℕ) :
    padicNorm p ((Delta n h).coeff k) ≤ (p : ℚ) ^ (2 * h * levU h p + padicValNat p h.factorial) := by
  classical
  have hN : ∀ i ≤ h, padicValRat p (dPrime h i) ≤ (padicValNat p h.factorial : ℤ) := fun i hi => by
    rw [padicValRat_dPrime hp hi]; exact_mod_cast Vexp_le_factorial i hi
  have hG : ∀ i j : Fin (h + 1), vGeX p (padicValRat p (dPrime h i) - 2 * levU h p) (GramF n h i j) :=
    fun i j => by
      have hrc := rowClaim hp hpm hh (Nat.lt_succ_iff.mp i.isLt) (Nat.lt_succ_iff.mp j.isLt)
      exact vGeX_add (vGeX_C hrc.1) (vGeX_X_mul (vGeX_C hrc.2))
  set S : ℤ := ∑ i : Fin (h + 1), padicValRat p (dPrime h i) with hS
  set L : ℤ := (levU h p : ℤ) with hL
  set V : ℤ := (padicValNat p h.factorial : ℤ) with hV
  have hadj : ∀ a b : Fin (h + 1), vGeX p (S - 2 * h * L - V) ((GramF n h).adjugate a b) := by
    intro a b
    rw [Matrix.adjugate_apply]
    have hdet := vGeX_det (p := p) ((GramF n h).updateRow b (Pi.single a 1))
      (fun i => if i = b then 0 else padicValRat p (dPrime h i) - 2 * L) (fun i j => by
        by_cases hib : i = b
        · subst hib
          rw [Matrix.updateRow_self, if_pos rfl]
          by_cases hja : j = a
          · subst hja; rw [Pi.single_eq_same]; exact vGeX_one
          · simp only [Pi.single_apply, hja, if_false]; exact Ti.L9.vGeX_zero' 0
        · rw [Matrix.updateRow_ne hib, if_neg hib]; exact hG i j)
    refine Ti.L9.vGeX_mono' ?_ hdet
    have hpt : ∀ i : Fin (h + 1), (if i = b then (0 : ℤ) else padicValRat p (dPrime h i) - 2 * L) =
        (padicValRat p (dPrime h i) - 2 * L) - if i = b then padicValRat p (dPrime h b) - 2 * L else 0 := by
      intro i; split_ifs with hib
      · subst hib; ring
      · ring
    rw [sum_congr rfl (fun i _ => hpt i), sum_sub_distrib, sum_ite_eq' univ b, if_pos (mem_univ b),
      sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← hS]
    have := hN b (Nat.lt_succ_iff.mp b.isLt)
    push_cast
    linarith
  have hsum : vGeX p (S - 2 * h * L - V) (∑ a, ∑ b, (GramF n h).adjugate a b) :=
    vGeX_sum _ _ (fun a _ => vGeX_sum _ _ (fun b _ => hadj a b))
  have hsgn : vGeX p 0 (C ((-1 : (Qt n)) ^ ((h + 1) * h / 2))) :=
    vGeX_C (vGe_of_pInt (pInt_pow (pInt_neg pInt_one) _))
  set P : ℚ := ∏ i ∈ range (h + 1), dPrime h i with hP
  have hP0 : P ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => Chi2U.LB.dPrime_ne_zero h i)
  have hLB : vGeX p (S - 2 * h * L - V) ((Delta n h).map (algebraMap ℚ (Qt n)) * C ((P : ℚ) : (Qt n))) := by
    have e : ((P : ℚ) : (Qt n)) = ∏ i ∈ range (h + 1), ((dPrime h i : ℚ) : (Qt n)) := by rw [hP, Rat.cast_prod]
    rw [e, lemmaB hh]
    have := vGeX_mul hsgn hsum
    rwa [zero_add] at this
  have hPv : padicValRat p P⁻¹ = -S := by
    rw [padicValRat.inv, hP, padicValRat_prod' _ _ (fun i _ => Chi2U.LB.dPrime_ne_zero h i), hS,
      Fin.sum_univ_eq_sum_range (fun i => padicValRat p (dPrime h i))]
  have hinv : vGeX p (-S) (C ((P⁻¹ : ℚ) : (Qt n))) := vGeX_C (by rw [← hPv]; exact vGe_ratCast _)
  have hΔ : vGeX p (S - 2 * h * L - V + -S) ((Delta n h).map (algebraMap ℚ (Qt n))) := by
    have := vGeX_mul hLB hinv
    have e : (Delta n h).map (algebraMap ℚ (Qt n)) * C ((P : ℚ) : (Qt n)) * C ((P⁻¹ : ℚ) : (Qt n)) =
        (Delta n h).map (algebraMap ℚ (Qt n)) := by
      rw [mul_assoc, ← C_mul, ← Rat.cast_mul, mul_inv_cancel₀ hP0, Rat.cast_one, C_1, mul_one]
    rwa [e] at this
  have hcoef := padicNorm_coeff_of_vGeX_map hΔ k
  rw [show -(S - 2 * h * L - V + -S) = ((2 * h * levU h p + padicValNat p h.factorial : ℕ) : ℤ) by
    rw [hL, hV]; push_cast; ring, zpow_natCast] at hcoef
  exact hcoef

end Ti
end Chi2U
