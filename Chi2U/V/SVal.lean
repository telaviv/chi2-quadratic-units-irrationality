/-
# Lemma S: the local valuation facts

* `vGe_Lmom_special`: the Mahler form with denominators `(2m)^{b+1}` (`Mahler.Lmom_eq_mahler`) gives, for any prime
  `p` and `F` with `p`-integral values at the odd integers and `F = 0 ∨ deg F < r`,
  `v_p(Lmom F) ≥ −v_p(2m)·r` (PROOF_V §3.2; the paper's extra `v_p(b!)` is not needed).
* `vGe_muPoly_divD`: hence `v_p(μ(t^n div D)) ≥ −v_p(2m)·(n − K)₊` (`K = h + 1`): the polynomial part `𝒫_{ij}`.
* `vGe_Psum_levels`: `v_p(P(x_m)) ≥ −Σ_{l ∈ levelsV} w_{p^l}(m)` (all levels; Lemma8One has the one-level case).
* `padicValRat_pole_sub`: `v_p(x_m − x_l) = #{l' ∈ levelsV : p^{l'} ∣ m − l}` for odd `p`, `m ≠ l ≤ h`.
-/
import Chi2U.V.SNewton

namespace Chi2U
namespace V

open Polynomial Finset

variable {mz : ℕ} [Fact (1 ≤ mz)] {p : ℕ} [hpF : Fact p.Prime]

/-! ### The polynomial part -/

lemma padicValRat_one_div_pow {n : ℕ} (hn : n ≠ 0) (b : ℕ) :
    padicValRat p (1 / (n : ℚ) ^ b) = -(b * padicValRat p n) := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  rw [padicValRat.div one_ne_zero (pow_ne_zero _ hn'), padicValRat.one, padicValRat.pow, zero_sub]

/-- Mahler form with denominators `(2m)^{b+1}`: `v_p(Lmom F) ≥ −v_p(2m)·r`. -/
theorem vGe_Lmom_special (F : ℚ[X]) (r : ℕ)
    (hF : ∀ k : ℕ, padicNorm p (F.eval (2 * (k : ℚ) + 1)) ≤ 1) (hr : F = 0 ∨ F.natDegree < r) :
    vGe p (-(padicValRat p ((2 * mz : ℕ) : ℚ) * r)) (Lmom mz F) := by
  rcases hr with rfl | hr
  · rw [map_zero]; exact vGe_zero _
  have h2m : (2 * mz : ℕ) ≠ 0 := by have := (Fact.out : 1 ≤ mz); omega
  have he0 : 0 ≤ padicValRat p ((2 * mz : ℕ) : ℚ) := by rw [padicValRat.of_nat]; positivity
  rw [Lmom_eq_mahler]
  refine vGe_sum _ _ (fun b hb => ?_)
  have hbr : b + 1 ≤ r := by have := mem_range.mp hb; omega
  have hm : padicNorm p (mahlerCoeff F b) ≤ 1 := by
    unfold mahlerCoeff
    refine padicNorm.sum_le' (fun k _ => ?_) zero_le_one
    rw [padicNorm.mul]
    have hint : padicNorm p ((-1 : ℚ) ^ (b - k) * (b.choose k : ℚ)) ≤ 1 := by
      have := padicNorm.of_int (p := p) ((-1 : ℤ) ^ (b - k) * (b.choose k : ℤ)); push_cast at this; exact this
    calc padicNorm p ((-1 : ℚ) ^ (b - k) * (b.choose k : ℚ)) * padicNorm p (F.eval (2 * (k : ℚ) + 1))
        ≤ 1 * 1 := mul_le_mul hint (hF k) (padicNorm.nonneg _) zero_le_one
      _ = 1 := one_mul _
  have h1 : vGe p 0 (mahlerCoeff F b : (Qd mz)) := vGe_of_pInt (pInt_ratCast hm)
  have h2 : vGe p 0 ((zK mz) ^ b) := vGe_of_pInt (pInt_pow pInt_zK b)
  have h3 := vGe_ratCast (mz := mz) (p := p) (1 / ((2 * mz : ℕ) : ℚ) ^ (b + 1))
  rw [padicValRat_one_div_pow h2m] at h3
  have e : (mahlerCoeff F b : (Qd mz)) * (zK mz) ^ b / ((2 * mz : ℕ) : Qd mz) ^ (b + 1) =
      (mahlerCoeff F b : (Qd mz)) * (zK mz) ^ b * ((1 / ((2 * mz : ℕ) : ℚ) ^ (b + 1) : ℚ) : Qd mz) := by
    push_cast; ring
  rw [e]
  refine vGe_mono ?_ (vGe_mul (vGe_mul h1 h2) h3)
  have hb' : ((b + 1 : ℕ) : ℤ) ≤ (r : ℤ) := by exact_mod_cast hbr
  have := mul_le_mul_of_nonneg_left hb' he0
  linarith

/-- `v_p(μ(t^n div D)) ≥ −v_p(2m)·(n − K)` (truncated subtraction, `K = h + 1`). -/
theorem vGe_muPoly_divD (h n : ℕ) :
    vGe p (-(padicValRat p ((2 * mz : ℕ) : ℚ) * ((n - (h + 1) : ℕ) : ℤ)))
      (muPoly mz ((X ^ n : ℚ[X]) /ₘ Dpoly h)) := by
  have hQ : (X ^ n : ℚ[X]) /ₘ Dpoly h = ((X ^ n : ℤ[X]) /ₘ l8DZ h).map (Int.castRingHom ℚ) := by
    rw [l8_Dpoly_eq, Polynomial.map_divByMonic _ l8_DZ_monic, Polynomial.map_pow, Polynomial.map_X]
  have hD := Dpoly_monic h
  unfold muPoly
  refine vGe_Lmom_special _ _ (fun k => ?_) ?_
  · rw [hQ, derivative_map]
    have e : (2 * (k : ℚ) + 1) = (((2 * k + 1 : ℕ) : ℤ) : ℚ) := by push_cast; ring
    rw [e, eval_intCast_map]
    simpa using padicNorm.of_int (p := p) _
  · by_cases hn : n < h + 1
    · left
      have : (X ^ n : ℚ[X]) /ₘ Dpoly h = 0 := by
        rw [divByMonic_eq_zero_iff hD, degree_X_pow, degree_eq_natDegree hD.ne_zero, natDegree_Dpoly]
        exact_mod_cast hn
      rw [this, derivative_zero]
    · have hdeg : ((X ^ n : ℚ[X]) /ₘ Dpoly h).natDegree = n - (h + 1) := by
        rw [natDegree_divByMonic _ hD, natDegree_X_pow, natDegree_Dpoly]
      by_cases h0 : ((X ^ n : ℚ[X]) /ₘ Dpoly h).natDegree = 0
      · left; exact derivative_of_natDegree_zero h0
      · right; rw [← hdeg]; exact natDegree_derivative_lt h0

/-! ### The partial sums, all levels -/

/-- `Σ_{l ∈ levelsV} w_{p^l}(m)`: the total pole-factor weight of atom `m`. -/
def wT (h p m : ℕ) : ℕ := ∑ l ∈ levelsV h p, wU h (p ^ l) m

lemma natAbs_poleZ_le {h m : ℕ} (hh : Even h) (hm : m ≤ h) : (poleZ h m).natAbs ≤ h := by
  obtain ⟨J, rfl⟩ := hh
  unfold poleZ
  have : (J + J) / 2 = J := by omega
  rw [this]
  omega

lemma two_padicValNat_le_wT {h m n : ℕ} (hh : Even h) (hm : m ≤ h) (hn0 : n ≠ 0)
    (hn : n < (poleZ h m).natAbs) : 2 * padicValNat p n ≤ wT h p m := by
  have hx := natAbs_poleZ_le hh hm
  have hsub : Icc 1 (padicValNat p n) ⊆ levelsV h p := by
    intro l hl
    have hl' := mem_Icc.mp hl
    have hdvd : p ^ l ∣ n := (pow_dvd_pow p hl'.2).trans pow_padicValNat_dvd
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
    have hlt := Nat.lt_pow_self (n := l) hpF.out.one_lt
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hl'.1, by omega⟩, by omega⟩
  have hw : ∀ l ∈ Icc 1 (padicValNat p n), wU h (p ^ l) m = 2 := by
    intro l hl
    have hl' := mem_Icc.mp hl
    have hdvd : p ^ l ∣ n := (pow_dvd_pow p hl'.2).trans pow_padicValNat_dvd
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
    unfold wU; rw [if_pos (by omega)]
  calc 2 * padicValNat p n = ∑ l ∈ Icc 1 (padicValNat p n), wU h (p ^ l) m := by
        rw [sum_congr rfl hw, sum_const, smul_eq_mul, Nat.card_Icc]; omega
    _ ≤ wT h p m := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

lemma padicNorm_inv_sq_levels {h m k : ℕ} (hh : Even h) (hm : m ≤ h) (hk : 2 * k + 1 < (poleZ h m).natAbs) :
    padicNorm p (1 / ((2 * k + 1 : ℕ) : ℚ) ^ 2) ≤ (p : ℚ) ^ (wT h p m : ℤ) := by
  have hn0 : ((2 * k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hpF.out.one_lt.le
  have hp0 : (p : ℚ) ≠ 0 := by positivity
  rw [padicNorm.div, padicNorm.one, sq, padicNorm.mul, padicNorm.eq_zpow_of_nonzero hn0, padicValRat.of_nat,
    ← zpow_add₀ hp0, one_div, ← zpow_neg]
  refine zpow_le_zpow_right₀ hp1 ?_
  have := two_padicValNat_le_wT (p := p) hh hm (by omega) hk
  omega

/-- `v_p(P(x_m)) ≥ −wT(m)` (all levels). -/
lemma vGe_Psum_levels {h m : ℕ} (hh : Even h) (hm : m ≤ h) :
    vGe p (-(wT h p m : ℤ)) (Psum mz (poleZ h m)) := by
  have hterm : ∀ k ∈ range ((poleZ h m).natAbs / 2), ∀ u : (Qd mz), pInt p u →
      vGe p (-(wT h p m : ℤ)) (u / ((2 * k + 1 : ℕ) : (Qd mz)) ^ 2) := by
    intro k hk u hu
    have hk' : 2 * k + 1 < (poleZ h m).natAbs := by have := mem_range.mp hk; omega
    have e : u / ((2 * k + 1 : ℕ) : (Qd mz)) ^ 2 = u * (((1 / ((2 * k + 1 : ℕ) : ℚ) ^ 2 : ℚ)) : (Qd mz)) := by
      push_cast; ring
    rw [e]
    have := vGe_mul (vGe_of_pInt hu) (vGe_ratCast_of_padicNorm (n := -(wT h p m : ℤ))
      (by rw [neg_neg]; exact padicNorm_inv_sq_levels hh hm hk'))
    simpa using this
  unfold Psum
  split_ifs
  · exact vGe_sum _ _ (fun k hk => hterm k hk _ (pInt_pow pInt_zK _))
  · exact vGe_neg (vGe_sum _ _ (fun k hk => hterm k hk _ (by rw [← inv_pow]; exact pInt_pow pInt_zK_inv _)))

/-! ### Pole differences -/

/-- `#{l' ∈ levelsV : m ≡ l mod p^{l'}}`. -/
def vmult (h p m l : ℕ) : ℕ := ((levelsV h p).filter (fun e => m % p ^ e = l % p ^ e)).card

lemma vmult_comm (h p m l : ℕ) : vmult h p m l = vmult h p l m := by
  unfold vmult; congr 1; exact filter_congr (fun _ _ => eq_comm)

lemma padicValRat_pole_sub (hp2 : p ≠ 2) {h m l : ℕ} (hm : m ≤ h) (hl : l ≤ h) (hml : m ≠ l) :
    padicValRat p ((poleZ h m : ℚ) - poleZ h l) = vmult h p m l := by
  have hpp : p.Prime := hpF.out
  set N : ℤ := (m : ℤ) - l with hN
  have hN0 : N ≠ 0 := by omega
  have hNa : N.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hN0
  have hNh : N.natAbs ≤ h := by omega
  have e : ((poleZ h m : ℚ) - poleZ h l) = 2 * (N : ℚ) := by rw [LB.poleZ_sub, hN]; push_cast; ring
  have h2 : padicValRat p 2 = 0 := by
    have : padicValRat p ((2 : ℕ) : ℚ) = 0 := by
      rw [padicValRat.of_nat]
      exact_mod_cast padicValNat.eq_zero_of_not_dvd (fun hd =>
        hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp hd))
    exact_mod_cast this
  rw [e, padicValRat.mul (by norm_num) (by exact_mod_cast hN0), h2, zero_add, padicValRat.of_int]
  unfold padicValInt
  congr 1
  have hset : (levelsV h p).filter (fun e => m % p ^ e = l % p ^ e) = Icc 1 (padicValNat p N.natAbs) := by
    ext e
    simp only [mem_filter, levelsV, mem_Icc]
    have hiff : m % p ^ e = l % p ^ e ↔ p ^ e ∣ N.natAbs := by
      rw [show (m % p ^ e = l % p ^ e) ↔ Nat.ModEq (p ^ e) l m from eq_comm, Nat.modEq_iff_dvd,
        ← Int.natAbs_dvd_natAbs]
      simp only [Int.natAbs_natCast]
      rw [show ((m : ℤ) - l).natAbs = N.natAbs from rfl]
    rw [hiff, padicValNat_dvd_iff_le hNa]
    constructor
    · rintro ⟨⟨⟨h1, _⟩, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      have hdvd : p ^ e ∣ N.natAbs := (padicValNat_dvd_iff_le hNa).mpr h3
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hNa) hdvd
      have hlt := Nat.lt_pow_self (n := e) hpp.one_lt
      exact ⟨⟨⟨h1, by omega⟩, by omega⟩, h3⟩
  rw [vmult, hset, Nat.card_Icc]
  omega

/-- `v_p(D′(x_m)) = Σ_{l ≠ m} vmult(m, l)`. -/
lemma padicValRat_dPrime (hp2 : p ≠ 2) {h m : ℕ} (hm : m ≤ h) :
    padicValRat p (dPrime h m) = ∑ l ∈ range (h + 1), if l = m then 0 else (vmult h p m l : ℤ) := by
  unfold dPrime
  rw [l8_padicValRat_prod _ _ (fun l _ => by
    split_ifs with hl
    · exact one_ne_zero
    · exact sub_ne_zero.mpr (fun e => hl (l8_poleZ_inj e).symm))]
  refine sum_congr rfl (fun l hl => ?_)
  split_ifs with hlm
  · simp
  · exact padicValRat_pole_sub hp2 hm (Nat.lt_succ_iff.mp (mem_range.mp hl)) (Ne.symm hlm)

end V
end Chi2U
