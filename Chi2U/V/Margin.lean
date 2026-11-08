/-
# Theorem V: the margin inequality (PROOF_V §0, §7)

`margin_V_proof`: `α(m) + Φ_L − L(m)/2 < 0` for `m ≥ 2`, `m ∉ {3, 5, 7, 9, 15}` (used as `margin_V` in `Interface.lean`).

Route (PROOF_V §7 with Lean's constant `Φ_L = −1.3538792`):
* `log m = v₂(m) log 2 + Σ_{p ∈ oddDiv m} v_p(m) log p` (`log_nat_eq`), so
  `cSV m = ¼ (log m − v₂(m) log 2) + Σ_{p ∣ m odd} log p/(4(p − 1))` (`cSV_eq`), and the last sum is
  `≤ ⅛ Σ v_p(m) log p` (`sum_g_le`, `p ≥ 3`);
* `L(m) ≥ log(2m) − log(2 + √5)` (`Lshift_ge`, from `z_m ≤ 1/(2m)`), `log(2 + √5) ≤ (25/12) log 2`;
* even `m ≥ 4`: `M ≤ 4/3 + Φ_L + (25/24 − 9/8) log 2 < 0`; odd `m ≥ 69`: `M ≤ K₀ − ⅛ log m < 0`
  (`log 69 ≥ (226/37) log 2`); `m = 2`: `M = 4/3 + Φ_L` exactly; odd `11 ≤ m ≤ 67`: `M ≤ K₀ − ¼ log m +
  Σ_{p ∣ m} log p/(4(p − 1))` checked case by case (`bsmall_*`) with `log n` bounded by `2^j ≤ n^k` / `n^k ≤ 2^j`
  (exponents from a Python search; `Real.log_two_gt_d9`, `Real.log_two_lt_d9`).
Departure from PROOF_V: none in substance (the closed form is used with `log m` in place of `log q`, and the
finite range is odd `m ≤ 67`).
-/
import Chi2U.V.Defs

set_option exponentiation.threshold 1000

namespace Chi2U
namespace V

open Finset

/-! ## Log bounds from powers of two -/

lemma log_ge_of_pow {n j k : ℕ} (hk : 0 < k) (h : 2 ^ j ≤ n ^ k) :
    (j : ℝ) / k * Real.log 2 ≤ Real.log n := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · rw [zero_pow hk.ne'] at h; exact absurd h (Nat.not_le.mpr (by positivity))
    · exact h0
  have h' : ((2 : ℝ)) ^ j ≤ (n : ℝ) ^ k := by exact_mod_cast h
  have := Real.log_le_log (by positivity) h'
  rw [Real.log_pow, Real.log_pow] at this
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_mul_eq_mul_div, div_le_iff₀ hk']
  linarith

lemma log_le_of_pow {n j k : ℕ} (hn : 0 < n) (hk : 0 < k) (h : n ^ k ≤ 2 ^ j) :
    Real.log n ≤ (j : ℝ) / k * Real.log 2 := by
  have h' : (n : ℝ) ^ k ≤ (2 : ℝ) ^ j := by exact_mod_cast h
  have := Real.log_le_log (by positivity) h'
  rw [Real.log_pow, Real.log_pow] at this
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_mul_eq_mul_div, le_div_iff₀ hk']
  linarith

/-- `log(√5 + 2) ≤ (25/12) log 2` (`(2.23607 + 2)^12 ≤ 2^25`). -/
lemma log_sqrt5_add_two_le : Real.log (Real.sqrt 5 + 2) ≤ 25 / 12 * Real.log 2 := by
  have hs : Real.sqrt 5 ≤ 223607 / 100000 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have h0 : 0 ≤ Real.sqrt 5 + 2 := by positivity
  have h1 : (Real.sqrt 5 + 2) ^ 12 ≤ (2 : ℝ) ^ 25 :=
    (pow_le_pow_left₀ h0 (by linarith : Real.sqrt 5 + 2 ≤ 423607 / 100000) 12).trans (by norm_num)
  have := Real.log_le_log (by positivity) h1
  rw [Real.log_pow, Real.log_pow] at this
  push_cast at this
  linarith

/-! ## `log m` through the factorisation -/

lemma mem_oddDiv {m p : ℕ} (hp : p ∈ oddDiv m) : p.Prime ∧ p ≠ 2 ∧ p ∣ m ∧ m ≠ 0 := by
  obtain ⟨h1, h2⟩ := mem_filter.mp hp
  obtain ⟨a, b, c⟩ := Nat.mem_primeFactors.mp h1
  exact ⟨a, h2, b, c⟩

/-- `log m = v₂(m) log 2 + Σ_{p ∈ oddDiv m} v_p(m) log p`. -/
lemma log_nat_eq {m : ℕ} (hm : m ≠ 0) :
    Real.log m = (padicValNat 2 m : ℝ) * Real.log 2 +
      ∑ p ∈ oddDiv m, (padicValNat p m : ℝ) * Real.log p := by
  have hprod : (m : ℝ) = ∏ p ∈ m.primeFactors, ((p : ℝ) ^ (m.factorization p)) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hm]
    rw [Finsupp.prod, Nat.support_factorization, Nat.cast_prod]
    simp only [Nat.cast_pow]
  have hne : ∀ p ∈ m.primeFactors, ((p : ℝ) ^ (m.factorization p)) ≠ 0 := fun p hp =>
    pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)
  rw [hprod, Real.log_prod hne]
  simp only [Real.log_pow]
  rw [← sum_filter_add_sum_filter_not m.primeFactors (fun p => p = 2)]
  congr 1
  · rw [filter_eq']
    split_ifs with h2
    · rw [sum_singleton, Nat.factorization_def m Nat.prime_two, Nat.cast_ofNat]
    · rw [sum_empty]
      have : ¬ 2 ∣ m := fun hd => h2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hd, hm⟩)
      rw [padicValNat.eq_zero_of_not_dvd this]; simp
  · apply sum_congr rfl
    intro p hp
    rw [Nat.factorization_def m (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)]

/-- `cSV m = ¼ Σ v_p log p + Σ log p/(4(p − 1))`. -/
lemma cSV_eq (m : ℕ) : cSV m = 1 / 4 * ∑ p ∈ oddDiv m, (padicValNat p m : ℝ) * Real.log p +
    ∑ p ∈ oddDiv m, Real.log p / (4 * ((p : ℝ) - 1)) := by
  unfold cSV
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  ring

/-- `Σ_{p ∣ m odd} log p/(4(p − 1)) ≤ ⅛ Σ v_p(m) log p` (`p ≥ 3`, `v_p ≥ 1`). -/
lemma sum_g_le (m : ℕ) : ∑ p ∈ oddDiv m, Real.log p / (4 * ((p : ℝ) - 1)) ≤
    1 / 8 * ∑ p ∈ oddDiv m, (padicValNat p m : ℝ) * Real.log p := by
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  obtain ⟨hpp, hp2, hpm, hm0⟩ := mem_oddDiv hp
  have := Fact.mk hpp
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hpp.two_le; omega)
  have hv : (1 : ℝ) ≤ padicValNat p m := by exact_mod_cast one_le_padicValNat_of_dvd hm0 hpm
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.2 hv) hl,
    mul_nonneg (mul_nonneg (sub_nonneg.2 hv) hl) (by linarith : (0 : ℝ) ≤ p - 3),
    mul_nonneg hl (by linarith : (0 : ℝ) ≤ p - 3)]

/-! ## The shift -/

lemma zU_le_inv (m : ℕ) (hm : 1 ≤ m) : zU m ≤ 1 / (2 * m) := by
  unfold zU
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs : Real.sqrt ((m : ℝ) ^ 2 + 1) * Real.sqrt ((m : ℝ) ^ 2 + 1) = (m : ℝ) ^ 2 + 1 :=
    Real.mul_self_sqrt (by positivity)
  have hsm : (m : ℝ) < Real.sqrt ((m : ℝ) ^ 2 + 1) := (Real.lt_sqrt (by positivity)).mpr (by linarith)
  rw [le_div_iff₀ (by positivity)]
  nlinarith

lemma log_zU_two : Real.log (zU 2) = -Real.log (Real.sqrt 5 + 2) := by
  have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 5 + 2 := by positivity
  have e : zU 2 = (Real.sqrt 5 + 2)⁻¹ := by
    rw [zU_two]
    exact eq_inv_of_mul_eq_one_left (by linear_combination h5)
  rw [e, Real.log_inv]

/-- `L(m) ≥ log(2m) − log(2 + √5)`. -/
lemma Lshift_ge (m : ℕ) (hm : 1 ≤ m) :
    Real.log 2 + Real.log m - Real.log (Real.sqrt 5 + 2) ≤ Lshift m := by
  have : Fact (1 ≤ m) := ⟨hm⟩
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 := Real.log_le_log zU_pos (zU_le_inv m hm)
  rw [one_div, Real.log_inv, Real.log_mul (by norm_num) hm'.ne'] at h1
  unfold Lshift
  rw [log_zU_two]
  linarith

/-! ## The finite cases `11 ≤ m ≤ 67` odd -/

/-- The bound for odd `m` (with `log(2 + √5) ≤ (25/12) log 2` already used). -/
def Bsmall (m : ℕ) : Prop :=
  4 / 3 + PhiL - Real.log 2 / 4 + 25 / 24 * Real.log 2 - Real.log (m : ℝ) / 4 +
    ∑ p ∈ oddDiv m, Real.log (p : ℝ) / (4 * ((p : ℝ) - 1)) < 0

macro "bsmall_close" : tactic =>
  `(tactic| (unfold PhiL; linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]))

lemma bsmall_11 : Bsmall 11 := by
  have e : oddDiv 11 = {11} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (38 : ℝ) / 11 * Real.log 2 ≤ Real.log ((11 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h11 : Real.log ((11 : ℕ) : ℝ) ≤ (45 : ℝ) / 13 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_13 : Bsmall 13 := by
  have e : oddDiv 13 = {13} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (37 : ℝ) / 10 * Real.log 2 ≤ Real.log ((13 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h13 : Real.log ((13 : ℕ) : ℝ) ≤ (63 : ℝ) / 17 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_17 : Bsmall 17 := by
  have e : oddDiv 17 = {17} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (49 : ℝ) / 12 * Real.log 2 ≤ Real.log ((17 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h17 : Real.log ((17 : ℕ) : ℝ) ≤ (45 : ℝ) / 11 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_19 : Bsmall 19 := by
  have e : oddDiv 19 = {19} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (89 : ℝ) / 21 * Real.log 2 ≤ Real.log ((19 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h19 : Real.log ((19 : ℕ) : ℝ) ≤ (17 : ℝ) / 4 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_21 : Bsmall 21 := by
  have e : oddDiv 21 = {3, 7} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (57 : ℝ) / 13 * Real.log 2 ≤ Real.log ((21 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h3 : Real.log ((3 : ℕ) : ℝ) ≤ (27 : ℝ) / 17 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  have h7 : Real.log ((7 : ℕ) : ℝ) ≤ (45 : ℝ) / 16 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_insert (by decide), sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_23 : Bsmall 23 := by
  have e : oddDiv 23 = {23} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (104 : ℝ) / 23 * Real.log 2 ≤ Real.log ((23 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h23 : Real.log ((23 : ℕ) : ℝ) ≤ (68 : ℝ) / 15 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_25 : Bsmall 25 := by
  have e : oddDiv 25 = {5} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (51 : ℝ) / 11 * Real.log 2 ≤ Real.log ((25 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h5 : Real.log ((5 : ℕ) : ℝ) ≤ (72 : ℝ) / 31 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_27 : Bsmall 27 := by
  have e : oddDiv 27 = {3} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (19 : ℝ) / 4 * Real.log 2 ≤ Real.log ((27 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h3 : Real.log ((3 : ℕ) : ℝ) ≤ (27 : ℝ) / 17 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_29 : Bsmall 29 := by
  have e : oddDiv 29 = {29} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (34 : ℝ) / 7 * Real.log 2 ≤ Real.log ((29 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h29 : Real.log ((29 : ℕ) : ℝ) ≤ (73 : ℝ) / 15 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_31 : Bsmall 31 := by
  have e : oddDiv 31 = {31} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (89 : ℝ) / 18 * Real.log 2 ≤ Real.log ((31 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h31 : Real.log ((31 : ℕ) : ℝ) ≤ (109 : ℝ) / 22 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_33 : Bsmall 33 := by
  have e : oddDiv 33 = {3, 11} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (116 : ℝ) / 23 * Real.log 2 ≤ Real.log ((33 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h3 : Real.log ((3 : ℕ) : ℝ) ≤ (27 : ℝ) / 17 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  have h11 : Real.log ((11 : ℕ) : ℝ) ≤ (45 : ℝ) / 13 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_insert (by decide), sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_35 : Bsmall 35 := by
  have e : oddDiv 35 = {5, 7} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (41 : ℝ) / 8 * Real.log 2 ≤ Real.log ((35 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h5 : Real.log ((5 : ℕ) : ℝ) ≤ (72 : ℝ) / 31 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  have h7 : Real.log ((7 : ℕ) : ℝ) ≤ (45 : ℝ) / 16 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_insert (by decide), sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_37 : Bsmall 37 := by
  have e : oddDiv 37 = {37} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (26 : ℝ) / 5 * Real.log 2 ≤ Real.log ((37 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h37 : Real.log ((37 : ℕ) : ℝ) ≤ (73 : ℝ) / 14 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_39 : Bsmall 39 := by
  have e : oddDiv 39 = {3, 13} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (95 : ℝ) / 18 * Real.log 2 ≤ Real.log ((39 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h3 : Real.log ((3 : ℕ) : ℝ) ≤ (27 : ℝ) / 17 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  have h13 : Real.log ((13 : ℕ) : ℝ) ≤ (63 : ℝ) / 17 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_insert (by decide), sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_41 : Bsmall 41 := by
  have e : oddDiv 41 = {41} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (75 : ℝ) / 14 * Real.log 2 ≤ Real.log ((41 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h41 : Real.log ((41 : ℕ) : ℝ) ≤ (59 : ℝ) / 11 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_43 : Bsmall 43 := by
  have e : oddDiv 43 = {43} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (65 : ℝ) / 12 * Real.log 2 ≤ Real.log ((43 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h43 : Real.log ((43 : ℕ) : ℝ) ≤ (38 : ℝ) / 7 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_45 : Bsmall 45 := by
  have e : oddDiv 45 = {3, 5} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (159 : ℝ) / 29 * Real.log 2 ≤ Real.log ((45 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h3 : Real.log ((3 : ℕ) : ℝ) ≤ (27 : ℝ) / 17 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  have h5 : Real.log ((5 : ℕ) : ℝ) ≤ (72 : ℝ) / 31 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_insert (by decide), sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_47 : Bsmall 47 := by
  have e : oddDiv 47 = {47} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (61 : ℝ) / 11 * Real.log 2 ≤ Real.log ((47 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h47 : Real.log ((47 : ℕ) : ℝ) ≤ (50 : ℝ) / 9 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_49 : Bsmall 49 := by
  have e : oddDiv 49 = {7} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (101 : ℝ) / 18 * Real.log 2 ≤ Real.log ((49 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h7 : Real.log ((7 : ℕ) : ℝ) ≤ (45 : ℝ) / 16 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_51 : Bsmall 51 := by
  have e : oddDiv 51 = {3, 17} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (17 : ℝ) / 3 * Real.log 2 ≤ Real.log ((51 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h3 : Real.log ((3 : ℕ) : ℝ) ≤ (27 : ℝ) / 17 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  have h17 : Real.log ((17 : ℕ) : ℝ) ≤ (45 : ℝ) / 11 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_insert (by decide), sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_53 : Bsmall 53 := by
  have e : oddDiv 53 = {53} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (63 : ℝ) / 11 * Real.log 2 ≤ Real.log ((53 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h53 : Real.log ((53 : ℕ) : ℝ) ≤ (86 : ℝ) / 15 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_55 : Bsmall 55 := by
  have e : oddDiv 55 = {5, 11} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (52 : ℝ) / 9 * Real.log 2 ≤ Real.log ((55 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h5 : Real.log ((5 : ℕ) : ℝ) ≤ (72 : ℝ) / 31 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  have h11 : Real.log ((11 : ℕ) : ℝ) ≤ (45 : ℝ) / 13 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_insert (by decide), sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_57 : Bsmall 57 := by
  have e : oddDiv 57 = {3, 19} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (99 : ℝ) / 17 * Real.log 2 ≤ Real.log ((57 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h3 : Real.log ((3 : ℕ) : ℝ) ≤ (27 : ℝ) / 17 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  have h19 : Real.log ((19 : ℕ) : ℝ) ≤ (17 : ℝ) / 4 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_insert (by decide), sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_59 : Bsmall 59 := by
  have e : oddDiv 59 = {59} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (47 : ℝ) / 8 * Real.log 2 ≤ Real.log ((59 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h59 : Real.log ((59 : ℕ) : ℝ) ≤ (53 : ℝ) / 9 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_61 : Bsmall 61 := by
  have e : oddDiv 61 = {61} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (77 : ℝ) / 13 * Real.log 2 ≤ Real.log ((61 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h61 : Real.log ((61 : ℕ) : ℝ) ≤ (89 : ℝ) / 15 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_63 : Bsmall 63 := by
  have e : oddDiv 63 = {3, 7} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (185 : ℝ) / 31 * Real.log 2 ≤ Real.log ((63 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h3 : Real.log ((3 : ℕ) : ℝ) ≤ (27 : ℝ) / 17 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  have h7 : Real.log ((7 : ℕ) : ℝ) ≤ (45 : ℝ) / 16 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_insert (by decide), sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_65 : Bsmall 65 := by
  have e : oddDiv 65 = {5, 13} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (271 : ℝ) / 45 * Real.log 2 ≤ Real.log ((65 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h5 : Real.log ((5 : ℕ) : ℝ) ≤ (72 : ℝ) / 31 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  have h13 : Real.log ((13 : ℕ) : ℝ) ≤ (63 : ℝ) / 17 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_insert (by decide), sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close

lemma bsmall_67 : Bsmall 67 := by
  have e : oddDiv 67 = {67} := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]
  have h0 : (97 : ℝ) / 16 * Real.log 2 ≤ Real.log ((67 : ℕ) : ℝ) := log_ge_of_pow (by norm_num) (by norm_num)
  have h67 : Real.log ((67 : ℕ) : ℝ) ≤ (85 : ℝ) / 14 * Real.log 2 := log_le_of_pow (by norm_num) (by norm_num) (by norm_num)
  unfold Bsmall; rw [e]
  rw [sum_singleton]
  simp only [Nat.cast_ofNat] at *
  bsmall_close


lemma bsmall_of {m : ℕ} (h1 : 2 ≤ m) (h2 : m ≤ 68) (hodd : ¬ 2 ∣ m)
    (hE : m ∉ ({3, 5, 7, 9, 15} : Finset ℕ)) : Bsmall m := by
  interval_cases m <;> first | omega | exact absurd (by decide) hE | exact bsmall_11 | exact bsmall_13 | exact bsmall_17 | exact bsmall_19 | exact bsmall_21 | exact bsmall_23 | exact bsmall_25 | exact bsmall_27 | exact bsmall_29 | exact bsmall_31 | exact bsmall_33 | exact bsmall_35 | exact bsmall_37 | exact bsmall_39 | exact bsmall_41 | exact bsmall_43 | exact bsmall_45 | exact bsmall_47 | exact bsmall_49 | exact bsmall_51 | exact bsmall_53 | exact bsmall_55 | exact bsmall_57 | exact bsmall_59 | exact bsmall_61 | exact bsmall_63 | exact bsmall_65 | exact bsmall_67

/-! ## The margin -/

lemma oddDiv_two : oddDiv 2 = ∅ := by simp [oddDiv, Nat.primeFactors]

/-- **The margin inequality** (PROOF_V §0, §7) with `Φ_L` (`margin_V`). -/
theorem margin_V_proof {m : ℕ} (hm : 2 ≤ m) (hE : m ∉ ({3, 5, 7, 9, 15} : Finset ℕ)) :
    alphaV m + (PhiL - Lshift m / 2) < 0 := by
  have hm0 : m ≠ 0 := by omega
  by_cases hm2 : m = 2
  · subst hm2
    have hc : cSV 2 = 0 := by unfold cSV; rw [oddDiv_two, sum_empty]
    have hn : nuV 2 = 2 := by unfold nuV; simp
    have hc2 : c2V 2 = 0 := by unfold c2V; rw [hn]; norm_num
    unfold alphaV Lshift PhiL
    rw [hc, hc2, sub_self]
    norm_num
  have hLS := log_sqrt5_add_two_le
  have hL := Lshift_ge m (by omega)
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hlog := log_nat_eq hm0
  have hG := sum_g_le m
  have hc := cSV_eq m
  have hc2 : c2V m = |(padicValNat 2 m : ℝ) - 1| * Real.log 2 / 4 := by
    unfold c2V nuV; push_cast
    rw [show (1 : ℝ) + (padicValNat 2 m : ℝ) - 2 = (padicValNat 2 m : ℝ) - 1 by ring]
  set a := padicValNat 2 m with ha
  set T := ∑ p ∈ oddDiv m, (padicValNat p m : ℝ) * Real.log p with hT
  set G := ∑ p ∈ oddDiv m, Real.log p / (4 * ((p : ℝ) - 1)) with hGdef
  unfold alphaV
  rw [hc, hc2]
  by_cases h2 : 2 ∣ m
  · -- even `m ≥ 4`
    have := Fact.mk Nat.prime_two
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast one_le_padicValNat_of_dvd hm0 h2
    have hm4 : (4 : ℝ) ≤ m := by
      have : 4 ≤ m := by obtain ⟨k, rfl⟩ := h2; omega
      exact_mod_cast this
    have hlm : 2 * Real.log 2 ≤ Real.log m := by
      have : Real.log 4 ≤ Real.log m := Real.log_le_log (by norm_num) hm4
      have e : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith
    have hab : |(a : ℝ) - 1| = a - 1 := abs_of_nonneg (by linarith)
    rw [hab]
    have hal : Real.log 2 ≤ a * Real.log 2 := by nlinarith
    unfold PhiL
    nlinarith
  · -- odd `m`
    have ha0 : a = 0 := padicValNat.eq_zero_of_not_dvd h2
    rw [ha0] at hlog ⊢
    simp only [Nat.cast_zero, zero_sub, abs_neg, abs_one, zero_mul, zero_add] at hlog ⊢
    by_cases hm69 : 69 ≤ m
    · have h69 : (226 : ℝ) / 37 * Real.log 2 ≤ Real.log ((69 : ℕ) : ℝ) :=
        log_ge_of_pow (by norm_num) (by norm_num)
      have hlm : Real.log ((69 : ℕ) : ℝ) ≤ Real.log m :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hm69)
      have hT69 : 226 / 37 * Real.log 2 ≤ T := h69.trans (hlm.trans hlog.le)
      have hLm : Real.log 2 + T - 25 / 12 * Real.log 2 ≤ Lshift m := by linarith
      have hM : 4 / 3 + 1 * Real.log 2 / 4 + (1 / 4 * T + G) + (PhiL - Lshift m / 2) ≤
          4 / 3 + PhiL - Real.log 2 / 4 + 25 / 24 * Real.log 2 - T / 8 := by linarith
      have hK : 4 / 3 + PhiL - Real.log 2 / 4 + 25 / 24 * Real.log 2 - 226 / 37 * Real.log 2 / 8 < 0 := by
        unfold PhiL; linarith
      linarith
    · have hB := bsmall_of hm (by omega) h2 hE
      unfold Bsmall at hB
      linarith

end V
end Chi2U
