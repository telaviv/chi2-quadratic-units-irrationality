/-
# Theorem V_i: Lemma 8′ for one-level primes, `n_p ≤ A_K(p)` when `3p ≥ K` (PROOF_TI2 §2 → PROOF_V §3.1)

**Copy of `Chi2U/Arith/Lemma8One.lean`** for the Ti₂ machine, odd primes `p ∤ n` (ramified `p ∣ n² − 4` included).
Route as in the χ₂ file (Lagrange Gram matrix + Lemma B, crude bound `n_p ≤ Σ_i max(v_p(D′(x_i)), w_i)`, counting for
`3p ≥ K`). The `z`-free parts are reused from the χ₂ file (namespace `Chi2U`): `l8_poleZ_inj`, `l8_dPrime_ne_zero`,
`l8_cPole_fLag_mul`, `l8DZ`, `l8_Dpoly_eq`, `l8_fLag_eq`, `l8_DZ_monic`, `l8_padicNorm_inv_sq`, `l8_padicNorm_prod`,
`l8_zpow_prod`, `l8rho`, and the whole counting part (`l8_v_le`, `l8_class_le`, `l8_sum_le_AK`).

Changes against the χ₂ file: the pole factor `(−1)^{x/2} z^x` (`vGe_sgnPole`), the signs `χ₄(u) = (−1)^k` in `P(x)`
(units; no overall minus for `x > 0`), and the Ti₂ Mahler form in `l8_vGe_muPoly_fLag`.
-/
import Chi2U.Ti.OddPrimes

set_option linter.unusedSectionVars false

namespace Chi2U
namespace Ti

variable {n : ℕ} [Fact (3 ≤ n)]

open Polynomial Finset

variable {h p : ℕ}

/-! ### Integrality of the polynomial part -/

/-- `μ(f_i f_j div D)` is `p`-integral. -/
lemma l8_vGe_muPoly_fLag [Fact p.Prime] (hp : ¬ p ∣ n) (i j : ℕ) :
    vGe p 0 (muPoly n ((fLag h i * fLag h j) /ₘ Dpoly h)) := by
  have hQ : (fLag h i * fLag h j) /ₘ Dpoly h =
      ((l8fZ h i * l8fZ h j) /ₘ l8DZ h).map (Int.castRingHom ℚ) := by
    rw [l8_fLag_eq, l8_fLag_eq, l8_Dpoly_eq, ← Polynomial.map_mul, Polynomial.map_divByMonic _ l8_DZ_monic]
  rw [hQ, muPoly, derivative_map]
  refine vGe_Lmom_odd hp _ 0 (fun k => ?_)
  have e : (2 * (k : ℚ) + 1) = (((2 * k + 1 : ℕ) : ℤ) : ℚ) := by push_cast; ring
  rw [e, eval_intCast_map]
  simpa using padicNorm.of_int (p := p) _

/-! ### The partial sums `P(x_m)` for `3p ≥ K` -/

/-- `v_p(P(x_m)) ≥ −w(m)` for `3p ≥ K`. -/
lemma l8_vGe_Psum [Fact p.Prime] (h3 : h + 1 ≤ 3 * p) {m : ℕ} (hm : m ≤ h) :
    vGe p (-(wU h p m : ℤ)) (Psum n (poleZ h m)) := by
  have hterm : ∀ k ∈ range ((poleZ h m).natAbs / 2), ∀ u : (Qt n), pInt p u →
      vGe p (-(wU h p m : ℤ)) (u / ((2 * k + 1 : ℕ) : (Qt n)) ^ 2) := by
    intro k hk u hu
    have hk' : 2 * k + 1 < (poleZ h m).natAbs := by have := mem_range.mp hk; omega
    have e : u / ((2 * k + 1 : ℕ) : (Qt n)) ^ 2 = u * (((1 / ((2 * k + 1 : ℕ) : ℚ) ^ 2 : ℚ)) : (Qt n)) := by
      push_cast; ring
    rw [e]
    have := vGe_mul (vGe_of_pInt hu) (vGe_ratCast_of_padicNorm (v := -(wU h p m : ℤ))
      (by rw [neg_neg]; exact l8_padicNorm_inv_sq h3 hm hk'))
    simpa using this
  unfold Psum
  split_ifs
  · exact vGe_sum _ _ (fun k hk => hterm k hk _ (pInt_mul (pInt_pow (pInt_neg pInt_one) k) (pInt_pow pInt_zK _)))
  · exact vGe_sum _ _ (fun k hk => hterm k hk _ (pInt_mul (pInt_pow (pInt_neg pInt_one) k)
      (by rw [← inv_pow]; exact pInt_pow pInt_zK_inv _)))

/-! ### The crude bound `n_p ≤ Σ_i max(v_p(D′(x_i)), w_i)` -/

lemma l8_vGeX_mono {v w : ℤ} [Fact p.Prime] (hmn : w ≤ v) {F : (Qt n)[X]} (hF : vGeX p v F) : vGeX p w F :=
  fun k => vGe_mono hmn (hF k)

lemma l8_vGeX_zero [Fact p.Prime] (v : ℤ) : vGeX p v (0 : (Qt n)[X]) := fun k => by
  simpa using vGe_zero (p := p) v

section Crude

variable [Fact p.Prime] (hp : ¬ p ∣ n) (w : ℕ → ℤ) (hw0 : ∀ m, 0 ≤ w m)
  (hw : ∀ m ≤ h, vGe p (-w m) (Psum n (poleZ h m)))
include hp hw0 hw

lemma l8_vGe_A {i : ℕ} (hi : i ≤ h) (j : ℕ) : vGe p (l8rho h p w i) (Afun n h (fLag h i * fLag h j)) := by
  unfold Afun
  refine vGe_add (vGe_mono (min_le_left _ _) (l8_vGe_muPoly_fLag hp _ _)) (vGe_sum _ _ (fun m hm => ?_))
  have hm' : m ≤ h := Nat.lt_succ_iff.mp (mem_range.mp hm)
  rw [l8_cPole_fLag_mul hm']
  split_ifs with hc
  · obtain ⟨rfl, -⟩ := hc
    have := vGe_mul (vGe_mul (vGe_mul (vGe_ratCast (p := p) (dPrime h i)) (vGe_sgnPole (n := n) (poleZ h i)))
      (vGe_zK_zpow (p := p) (poleZ h i))) (hw i hi)
    refine vGe_mono ?_ this
    unfold l8rho; have := hw0 i; omega
  · rw [Rat.cast_zero, zero_mul, zero_mul, zero_mul]; exact vGe_zero _

omit hp hw in
lemma l8_vGe_B {i : ℕ} (j : ℕ) : vGe p (l8rho h p w i) (Bfun n h (fLag h i * fLag h j)) := by
  unfold Bfun
  refine vGe_neg (vGe_sum _ _ (fun m hm => ?_))
  have hm' : m ≤ h := Nat.lt_succ_iff.mp (mem_range.mp hm)
  rw [l8_cPole_fLag_mul hm']
  split_ifs with hc
  · obtain ⟨rfl, -⟩ := hc
    have := vGe_mul (vGe_mul (vGe_ratCast (p := p) (dPrime h i)) (vGe_sgnPole (n := n) (poleZ h i)))
      (vGe_zK_zpow (n := n) (p := p) (poleZ h i))
    refine vGe_mono ?_ this
    unfold l8rho; have := hw0 i; omega
  · rw [Rat.cast_zero, zero_mul, zero_mul]; exact vGe_zero _

lemma l8_vGeX_GramF (i j : Fin (h + 1)) : vGeX p (l8rho h p w i) (GramF n h i j) := by
  have hi : (i : ℕ) ≤ h := Nat.lt_succ_iff.mp i.isLt
  change vGeX p _ (LamX n h (fLag h i * fLag h j))
  unfold LamX
  exact vGeX_add (vGeX_C (l8_vGe_A hp w hw0 hw hi j)) (vGeX_X_mul (vGeX_C (l8_vGe_B w hw0 j)))

lemma l8_vGeX_adj (a b : Fin (h + 1)) :
    vGeX p (∑ i : Fin (h + 1), l8rho h p w i) ((GramF n h).adjugate a b) := by
  rw [Matrix.adjugate_apply]
  refine l8_vGeX_mono ?_ (vGeX_det _ (fun r : Fin (h + 1) => if r = b then 0 else l8rho h p w r) (fun r c => ?_))
  · refine sum_le_sum (fun r _ => ?_)
    split_ifs
    · exact min_le_left _ _
    · exact le_rfl
  · rw [Matrix.updateRow_apply]
    split_ifs with hr
    · rw [Pi.single_apply]
      split_ifs
      · exact vGeX_one
      · exact l8_vGeX_zero 0
    · exact l8_vGeX_GramF hp w hw0 hw r c

/-- **Crude bound** (any odd `p ∤ n`, any weights `w ≥ 0` with `v_p(P(x_m)) ≥ −w_m`):
`|c_k|_p ≤ p^{Σ_m max(v_p(D′(x_m)), w_m)}` for the coefficients of `Δ_h`. -/
theorem padicNorm_Delta_crude (hh : Even h) (k : ℕ) :
    padicNorm p ((Delta n h).coeff k) ≤
      (p : ℚ) ^ (∑ m ∈ range (h + 1), max (padicValRat p (dPrime h m)) (w m)) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hppos : (0 : ℚ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hS : vGeX p (∑ i : Fin (h + 1), l8rho h p w i)
      (C ((-1 : (Qt n)) ^ ((h + 1) * h / 2)) * ∑ a, ∑ b, (GramF n h).adjugate a b) := by
    have h1 : vGeX p 0 (C ((-1 : (Qt n)) ^ ((h + 1) * h / 2))) :=
      vGeX_C (vGe_of_pInt (pInt_pow (pInt_neg pInt_one) _))
    simpa using vGeX_mul h1 (vGeX_sum _ _ (fun a _ => vGeX_sum _ _ (fun b _ => l8_vGeX_adj hp w hw0 hw a b)))
  rw [← lemmaB hh] at hS
  have hk := padicNorm_le_of_vGe (n := n) (p := p) (r := (Delta n h).coeff k * ∏ i ∈ range (h + 1), dPrime h i) (by
    have := hS k
    rw [coeff_mul_C, coeff_map, eq_ratCast] at this
    push_cast
    exact this)
  rw [padicNorm.mul, l8_padicNorm_prod, prod_congr rfl (fun i _ => padicNorm.eq_zpow_of_nonzero
    (l8_dPrime_ne_zero h i)), l8_zpow_prod hp0] at hk
  have hexp : -(∑ i : Fin (h + 1), l8rho h p w i) + ∑ i ∈ range (h + 1), padicValRat p (dPrime h i) =
      ∑ m ∈ range (h + 1), max (padicValRat p (dPrime h m)) (w m) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => l8rho h p w i) (h + 1), ← sum_neg_distrib, ← sum_add_distrib]
    exact sum_congr rfl (fun m _ => by unfold l8rho; omega)
  rw [← hexp, zpow_add₀ hp0]
  have hpos : (0 : ℚ) < (p : ℚ) ^ (∑ i ∈ range (h + 1), padicValRat p (dPrime h i)) := zpow_pos hppos _
  calc padicNorm p ((Delta n h).coeff k)
      = padicNorm p ((Delta n h).coeff k) * (p : ℚ) ^ (∑ i ∈ range (h + 1), -padicValRat p (dPrime h i)) *
          (p : ℚ) ^ (∑ i ∈ range (h + 1), padicValRat p (dPrime h i)) := by
        rw [mul_assoc, ← zpow_add₀ hp0, sum_neg_distrib, neg_add_cancel, zpow_zero, mul_one]
    _ ≤ _ := by gcongr

end Crude

/-- **Lemma 8′ for `3p ≥ K`** (one level `e = 1` if `p < K`, none if `p ≥ K`): `|c_k|_p ≤ p^{A_K(p)}`; Ti₂ version of
`Chi2U.lemma8_one`. -/
theorem lemma8_one [Fact p.Prime] (hp : p ≠ 2) (hpm : ¬ p ∣ n) (hh : Even h) (h3 : h + 1 ≤ 3 * p) (k : ℕ) :
    padicNorm p ((Delta n h).coeff k) ≤ (p : ℚ) ^ AK h p := by
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  refine (padicNorm_Delta_crude hpm (fun m => (wU h p m : ℤ)) (fun m => by positivity)
    (fun m hm => l8_vGe_Psum h3 hm) hh k).trans ?_
  have hsum : (∑ m ∈ range (h + 1), max (padicValRat p (dPrime h m)) (wU h p m : ℤ)) ≤ (AK h p : ℤ) := by
    calc _ ≤ ∑ m ∈ range (h + 1), ((max ((clU h p (m % p)).card - 1) (wU h p m) : ℕ) : ℤ) :=
          sum_le_sum (fun m hm => by
            have := l8_v_le hp h3 (Nat.lt_succ_iff.mp (mem_range.mp hm))
            push_cast
            exact max_le_max this le_rfl)
      _ ≤ AK h p := by exact_mod_cast l8_sum_le_AK hp hh h3
  rw [← zpow_natCast]
  exact zpow_le_zpow_right₀ hp1 hsum

end Ti
end Chi2U
