/-
# Odd primes: Lemma 8′ (per-level bound) and Lemma 9′ (plateau bound) (PROOF_U §3.1–§3.5)

For an odd prime `p` (including `p = 5`: `z`, `y = z²`, `1 − y = 4z` are `p`-units) and even `h`:
* **Lemma 8′** (atom expansion, Laplace + Cauchy–Binet on `H = 𝒫 + Vᵀ diag(γ) V`):
  `n_p ≤ Σ_{e ≥ 1, p^e < K} A_K(p^e)`;
* **row claim** of Lemma 9′: `v_p(G^f_{ij}) ≥ N(i) − 2 lev*(p)`, `N(i) = v_p(D′(x_i))`;
* **Lemma 9′**: `n_p ≤ 2h·lev*(p) + v_p(h!)` (row claim + minor expansion of `𝟙ᵀ adj(G^f) 𝟙` + Lemma B);
(Lemma 8′ is in `Lemma8.lean`; the combination `n_p ≤ eOdd h p` in `OddExp.lean`.)
Here `n_p` is the Gauss exponent: `|c_k|_p ≤ p^{n_p}` for every coefficient `c_k` of `Δ_h`.

Proofs (this file: `rowClaim`, `lemma9`; level counting in `Lemma9Levels.lean`):
* The pole coefficients of `f_i f_j` are `c_m = [m = i = j] D′(x_i)` (`cPole_ff`), so `B(f_i f_j) = −[i = j] D′(x_i) z^{x_i}`
  and `A(f_i f_j) = μ(f_i f_j div D) + [i = j] D′(x_i) z^{x_i} P(x_i)`.
* `f_i f_j div D` is `F = Π_{m ≠ i,j}(t − x_m)` off the diagonal and the divided difference `DD_{x_i} f_i` on it.
  `vGe_Lmom_odd` (Mahler form, step 3) reduces `v_p(μ(·))` to the values of the derivative at odd `t ≥ 1`, which
  `prod_T_le` / `prod_DD_le` bound by `|D′(x_i)|_p p^{2 lev}` (steps 4–7, the transposition of χ₂'s Lemma 9).
* `v_p(P(x)) ≥ −2 lev*(p)` (`vGe_Psum`): only `1/n²` with odd `n < |x| ≤ h` occur.
* `lemma9`: `adj(G^f)_{ab} = det(G^f with row b replaced by e_a)`, Leibniz with row bounds (`vGeX_det`) gives
  `Σ_{i ≠ b}(N(i) − 2 lev) ≥ Σ_i N(i) − 2h lev − v_p(h!)`; Lemma B and division by `Π D′(x_i)` (valuation `Σ N(i)`)
  give the bound on the coefficients of `Δ_h`.
-/
import Chi2U.Arith.LemmaB
import Chi2U.Arith.VGe
import Chi2U.Arith.Lemma9Levels

namespace Chi2U

open Polynomial Finset

variable {h p : ℕ}

namespace L9

/-! ### The polynomials `f_i f_j` -/

/-- `F = Π_{m ≠ i, j}(t − x_m)`. -/
noncomputable def Fpoly (h i j : ℕ) : ℚ[X] :=
  ∏ m ∈ ((range (h + 1)).erase i).erase j, (X - C ((poleZ h m : ℤ) : ℚ))

lemma Dpoly_eq_mul_fLag {h i : ℕ} (hi : i ≤ h) : Dpoly h = (X - C ((poleZ h i : ℤ) : ℚ)) * fLag h i := by
  unfold Dpoly fLag
  exact (mul_prod_erase _ (fun m => X - C ((poleZ h m : ℤ) : ℚ)) (mem_range.mpr (Nat.lt_succ_of_le hi))).symm

lemma fLag_eq_mul_Fpoly {h i j : ℕ} (hj : j ≤ h) (hij : i ≠ j) :
    fLag h i = (X - C ((poleZ h j : ℤ) : ℚ)) * Fpoly h i j := by
  unfold fLag Fpoly
  exact (mul_prod_erase _ (fun m => X - C ((poleZ h m : ℤ) : ℚ))
    (mem_erase.mpr ⟨Ne.symm hij, mem_range.mpr (Nat.lt_succ_of_le hj)⟩)).symm

lemma Fpoly_comm (h i j : ℕ) : Fpoly h i j = Fpoly h j i := by unfold Fpoly; rw [erase_right_comm]

lemma fLag_mul_offdiag {h i j : ℕ} (hi : i ≤ h) (hj : j ≤ h) (hij : i ≠ j) :
    fLag h i * fLag h j = Dpoly h * Fpoly h i j := by
  rw [Dpoly_eq_mul_fLag hi, fLag_eq_mul_Fpoly hj hij, fLag_eq_mul_Fpoly hi (Ne.symm hij), Fpoly_comm h j i]
  ring

lemma divByMonic_offdiag {h i j : ℕ} (hi : i ≤ h) (hj : j ≤ h) (hij : i ≠ j) :
    (fLag h i * fLag h j) /ₘ Dpoly h = Fpoly h i j := by
  rw [fLag_mul_offdiag hi hj hij, mul_divByMonic_cancel_left _ (Dpoly_monic h)]

lemma natDegree_Dpoly (h : ℕ) : (Dpoly h).natDegree = h + 1 := by
  rw [Dpoly_eq_mul_fLag (Nat.zero_le h), (monic_X_sub_C _).natDegree_mul (LB.fLag_monic h 0),
    natDegree_X_sub_C, LB.natDegree_fLag (Nat.zero_le h)]
  ring

lemma divByMonic_diag {h i : ℕ} (hi : i ≤ h) :
    (fLag h i * fLag h i) /ₘ Dpoly h = DD ((poleZ h i : ℤ) : ℚ) (fLag h i) := by
  have h1 := X_sub_C_mul_DD ((poleZ h i : ℤ) : ℚ) (fLag h i)
  have e : fLag h i * fLag h i = Dpoly h * DD ((poleZ h i : ℤ) : ℚ) (fLag h i) +
      C ((fLag h i).eval ((poleZ h i : ℤ) : ℚ)) * fLag h i := by
    rw [Dpoly_eq_mul_fLag hi]
    linear_combination (-fLag h i) * h1
  rw [e, add_divByMonic, mul_divByMonic_cancel_left _ (Dpoly_monic h),
    (divByMonic_eq_zero_iff (Dpoly_monic h)).mpr ?_, add_zero]
  refine degree_lt_degree ((natDegree_C_mul_le _ _).trans_lt ?_)
  rw [LB.natDegree_fLag hi, natDegree_Dpoly]
  omega

/-! ### Pole coefficients -/

lemma cPole_ff {h : ℕ} (i j : ℕ) {m : ℕ} (hm : m ≤ h) :
    cPole h (fLag h i * fLag h j) m = if m = i ∧ m = j then dPrime h i else 0 := by
  unfold cPole
  rw [eval_mul, LB.eval_fLag i hm, LB.eval_fLag j hm]
  by_cases h1 : m = i
  · subst h1
    by_cases h2 : m = j
    · subst h2
      rw [if_pos rfl, if_pos ⟨rfl, rfl⟩, mul_div_assoc, div_self (LB.dPrime_ne_zero h m), mul_one]
    · rw [if_pos rfl, if_neg h2, if_neg (fun hh => h2 hh.2), mul_zero, zero_div]
  · rw [if_neg h1, zero_mul, zero_div, if_neg (fun hh => h1 hh.1)]

lemma sum_cPole_ff {h i : ℕ} (j : ℕ) (hi : i ≤ h) (F : ℕ → Q5) :
    ∑ m ∈ range (h + 1), (cPole h (fLag h i * fLag h j) m : Q5) * F m =
      if i = j then (dPrime h i : Q5) * F i else 0 := by
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
    Bfun h (fLag h i * fLag h j) = if i = j then -((dPrime h i : Q5) * zK ^ (poleZ h i)) else 0 := by
  have := sum_cPole_ff j hi (fun m => zK ^ (poleZ h m))
  unfold Bfun
  rw [this]
  split_ifs <;> simp

lemma Afun_ff {h i : ℕ} (j : ℕ) (hi : i ≤ h) :
    Afun h (fLag h i * fLag h j) = muPoly ((fLag h i * fLag h j) /ₘ Dpoly h) +
      if i = j then (dPrime h i : Q5) * zK ^ (poleZ h i) * Psum (poleZ h i) else 0 := by
  have := sum_cPole_ff j hi (fun m => zK ^ (poleZ h m) * Psum (poleZ h m))
  simp only [← mul_assoc] at this
  unfold Afun
  rw [this]

/-! ### Valuations -/

variable [hp : Fact p.Prime]

lemma vGeX_zero' (n : ℤ) : vGeX p n (0 : Q5[X]) := fun k => by rw [coeff_zero]; exact vGe_zero n

lemma vGeX_mono' {n m : ℤ} (hmn : m ≤ n) {F : Q5[X]} (hF : vGeX p n F) : vGeX p m F :=
  fun k => vGe_mono hmn (hF k)

lemma natAbs_poleZ_le (hh : Even h) {i : ℕ} (hi : i ≤ h) : (poleZ h i).natAbs ≤ h := by
  obtain ⟨r, rfl⟩ := hh
  unfold poleZ
  have : (r + r) / 2 = r := by omega
  rw [this]
  omega

/-- `v_p(P(x)) ≥ −2 lev*(p)` for `|x| ≤ h`. -/
lemma vGe_Psum {x : ℤ} (hx : x.natAbs ≤ h) : vGe p (-(2 * (levU h p : ℤ))) (Psum x) := by
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
    rw [show zK ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : Q5) ^ 2 = zK ^ ((2 * k + 1 : ℕ) : ℤ) *
        (((1 : ℚ) / ((2 * (k : ℚ) + 1) * (2 * k + 1)) : ℚ) : Q5) by rw [zpow_natCast]; push_cast; ring]
    simpa using vGe_mul (vGe_zK_zpow (p := p) _) (vGe_ratCast_of_padicNorm (hterm k hk))
  · refine vGe_neg (vGe_sum _ _ (fun k hk => ?_))
    rw [show (zK ^ (2 * k + 1))⁻¹ / ((2 * k + 1 : ℕ) : Q5) ^ 2 = zK ^ (-((2 * k + 1 : ℕ) : ℤ)) *
        (((1 : ℚ) / ((2 * (k : ℚ) + 1) * (2 * k + 1)) : ℚ) : Q5) by rw [zpow_neg, zpow_natCast]; push_cast; ring]
    simpa using vGe_mul (vGe_zK_zpow (p := p) _) (vGe_ratCast_of_padicNorm (hterm k hk))

lemma zpow_bound {i : ℕ} :
    (p : ℚ) ^ (-(padicValRat p (dPrime h i) - 2 * (levU h p : ℤ))) =
      padicNorm p (dPrime h i) * (p : ℚ) ^ (2 * levU h p) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [padicNorm.eq_zpow_of_nonzero (LB.dPrime_ne_zero h i), ← zpow_natCast, ← zpow_add₀ hp0]
  congr 1; push_cast; ring

section Deriv

variable (hp2 : p ≠ 2)
include hp2

lemma deriv_Fpoly_le {i : ℕ} (hi : i ≤ h) (j k : ℕ) :
    padicNorm p ((derivative (Fpoly h i j)).eval (2 * (k : ℚ) + 1)) ≤
      padicNorm p (dPrime h i) * (p : ℚ) ^ (2 * levU h p) := by
  have hB : 0 ≤ padicNorm p (dPrime h i) * (p : ℚ) ^ (2 * levU h p) :=
    mul_nonneg (padicNorm.nonneg _) (by positivity)
  unfold Fpoly
  rw [eval_derivative_prod]
  refine padicNorm.sum_le' (fun s _ => ?_) hB
  exact prod_T_le hp2 hi j s k _ (fun r hr h1 h2 h3 => by simp [mem_erase, *])

lemma deriv_DD_le {i : ℕ} (hi : i ≤ h) (k : ℕ) :
    padicNorm p ((derivative (DD ((poleZ h i : ℤ) : ℚ) (fLag h i))).eval (2 * (k : ℚ) + 1)) ≤
      padicNorm p (dPrime h i) * (p : ℚ) ^ (2 * levU h p) := by
  have hB : 0 ≤ padicNorm p (dPrime h i) * (p : ℚ) ^ (2 * levU h p) :=
    mul_nonneg (padicNorm.nonneg _) (by positivity)
  unfold fLag
  rw [DD_prod_rank _ (fun m => ((poleZ h m : ℤ) : ℚ)) (rk p (h + 1) i) _ (rk_injOn (h + 1) i), derivative_sum,
    eval_finsetSum]
  refine padicNorm.sum_le' (fun l hl => ?_) hB
  rw [derivative_C_mul, eval_mul, eval_C, eval_derivative_prod, mul_sum]
  exact padicNorm.sum_le' (fun s _ => prod_DD_le hp2 hi k l s hl) hB

end Deriv

lemma padicValRat_prod' (s : Finset ℕ) (f : ℕ → ℚ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [prod_insert ha, sum_insert ha, padicValRat.mul (hf a (mem_insert_self a s))
        (prod_ne_zero_iff.mpr (fun i hi => hf i (mem_insert_of_mem hi))),
        ih (fun i hi => hf i (mem_insert_of_mem hi))]

end L9

open L9

/-- **Row claim** of Lemma 9′ (both the `A` and the `B` part of `G^f_{ij}`). -/
theorem rowClaim [Fact p.Prime] (hp : p ≠ 2) (hh : Even h) {i j : ℕ} (hi : i ≤ h) (hj : j ≤ h) :
    vGe p (padicValRat p (dPrime h i) - 2 * levU h p) (Afun h (fLag h i * fLag h j)) ∧
      vGe p (padicValRat p (dPrime h i) - 2 * levU h p) (Bfun h (fLag h i * fLag h j)) := by
  have hmu : vGe p (padicValRat p (dPrime h i) - 2 * levU h p) (muPoly ((fLag h i * fLag h j) /ₘ Dpoly h)) := by
    refine vGe_Lmom_odd hp _ _ (fun k => ?_)
    rw [zpow_bound]
    by_cases hij : i = j
    · subst hij; rw [divByMonic_diag hi]; exact deriv_DD_le hp hi k
    · rw [divByMonic_offdiag hi hj hij]; exact deriv_Fpoly_le hp hi j k
  have hD : vGe p (padicValRat p (dPrime h i)) ((dPrime h i : Q5) * zK ^ poleZ h i) := by
    simpa using vGe_mul (vGe_ratCast (p := p) (dPrime h i)) (vGe_zK_zpow (p := p) (poleZ h i))
  constructor
  · rw [Afun_ff j hi]
    refine vGe_add hmu ?_
    split_ifs
    · have := vGe_mul hD (vGe_Psum (p := p) (natAbs_poleZ_le hh hi))
      convert this using 2
      ring
    · exact vGe_zero _
  · rw [Bfun_ff j hi]
    split_ifs
    · exact vGe_mono (by have := (levU h p).cast_nonneg (α := ℤ); linarith) (vGe_neg hD)
    · exact vGe_zero _

/-- **Lemma 9′** (plateau bound). -/
theorem lemma9 [Fact p.Prime] (hp : p ≠ 2) (hh : Even h) (k : ℕ) :
    padicNorm p ((Delta h).coeff k) ≤ (p : ℚ) ^ (2 * h * levU h p + padicValNat p h.factorial) := by
  classical
  have hN : ∀ i ≤ h, padicValRat p (dPrime h i) ≤ (padicValNat p h.factorial : ℤ) := fun i hi => by
    rw [padicValRat_dPrime hp hi]; exact_mod_cast Vexp_le_factorial i hi
  have hG : ∀ i j : Fin (h + 1), vGeX p (padicValRat p (dPrime h i) - 2 * levU h p) (GramF h i j) :=
    fun i j => by
      have hrc := rowClaim hp hh (Nat.lt_succ_iff.mp i.isLt) (Nat.lt_succ_iff.mp j.isLt)
      exact vGeX_add (vGeX_C hrc.1) (vGeX_X_mul (vGeX_C hrc.2))
  set S : ℤ := ∑ i : Fin (h + 1), padicValRat p (dPrime h i) with hS
  set L : ℤ := (levU h p : ℤ) with hL
  set V : ℤ := (padicValNat p h.factorial : ℤ) with hV
  have hadj : ∀ a b : Fin (h + 1), vGeX p (S - 2 * h * L - V) ((GramF h).adjugate a b) := by
    intro a b
    rw [Matrix.adjugate_apply]
    have hdet := vGeX_det (p := p) ((GramF h).updateRow b (Pi.single a 1))
      (fun i => if i = b then 0 else padicValRat p (dPrime h i) - 2 * L) (fun i j => by
        by_cases hib : i = b
        · subst hib
          rw [Matrix.updateRow_self, if_pos rfl]
          by_cases hja : j = a
          · subst hja; rw [Pi.single_eq_same]; exact vGeX_one
          · simp only [Pi.single_apply, hja, if_false]; exact vGeX_zero' 0
        · rw [Matrix.updateRow_ne hib, if_neg hib]; exact hG i j)
    refine vGeX_mono' ?_ hdet
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
  have hsum : vGeX p (S - 2 * h * L - V) (∑ a, ∑ b, (GramF h).adjugate a b) :=
    vGeX_sum _ _ (fun a _ => vGeX_sum _ _ (fun b _ => hadj a b))
  have hsgn : vGeX p 0 (C ((-1 : Q5) ^ ((h + 1) * h / 2))) :=
    vGeX_C (vGe_of_pInt (pInt_pow (pInt_neg pInt_one) _))
  set P : ℚ := ∏ i ∈ range (h + 1), dPrime h i with hP
  have hP0 : P ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => LB.dPrime_ne_zero h i)
  have hLB : vGeX p (S - 2 * h * L - V) ((Delta h).map (algebraMap ℚ Q5) * C ((P : ℚ) : Q5)) := by
    have e : ((P : ℚ) : Q5) = ∏ i ∈ range (h + 1), ((dPrime h i : ℚ) : Q5) := by rw [hP, Rat.cast_prod]
    rw [e, lemmaB hh]
    have := vGeX_mul hsgn hsum
    rwa [zero_add] at this
  have hPv : padicValRat p P⁻¹ = -S := by
    rw [padicValRat.inv, hP, padicValRat_prod' _ _ (fun i _ => LB.dPrime_ne_zero h i), hS,
      Fin.sum_univ_eq_sum_range (fun i => padicValRat p (dPrime h i))]
  have hinv : vGeX p (-S) (C ((P⁻¹ : ℚ) : Q5)) := vGeX_C (by rw [← hPv]; exact vGe_ratCast _)
  have hΔ : vGeX p (S - 2 * h * L - V + -S) ((Delta h).map (algebraMap ℚ Q5)) := by
    have := vGeX_mul hLB hinv
    have e : (Delta h).map (algebraMap ℚ Q5) * C ((P : ℚ) : Q5) * C ((P⁻¹ : ℚ) : Q5) =
        (Delta h).map (algebraMap ℚ Q5) := by
      rw [mul_assoc, ← C_mul, ← Rat.cast_mul, mul_inv_cancel₀ hP0, Rat.cast_one, C_1, mul_one]
    rwa [e] at this
  have hcoef := padicNorm_coeff_of_vGeX_map hΔ k
  rw [show -(S - 2 * h * L - V + -S) = ((2 * h * levU h p + padicValNat p h.factorial : ℕ) : ℤ) by
    rw [hL, hV]; push_cast; ring, zpow_natCast] at hcoef
  exact hcoef

end Chi2U
