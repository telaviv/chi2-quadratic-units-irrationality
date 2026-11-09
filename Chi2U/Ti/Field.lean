/-
# Theorem V_i: the field `ℚ(√d)`, `d = (n/2)² − 1`, the unit `z = n/2 − √d`, and the real embedding

**Copy of `Chi2U/Field.lean`** with the sign fixed (norm `+1` units; PROOF_TI2 §0–§1). Parametrised by the trace
`n : ℕ` of `z` with `[Fact (3 ≤ n)]`: `z = z_n = (n − √(n² − 4))/2`, `z + z⁻¹ = n`.

* `Qt n := QuadraticAlgebra ℚ ((n/2)² − 1) 0`: elements `re + im·√d`; a field (`(n/2)² − 1` is not a square for
  `n ≥ 3`: `not_isSquare_dT`).
* `sig`: the Galois conjugation `√d ↦ −√d`, as a ring hom.
* `zK n = n/2 − √d`: `z² − n·z + 1 = 0`, `z⁻¹ = n/2 + √d`, `σz = z⁻¹` (norm `+1`; χ₂'s was `σz = −z⁻¹`),
  `1 + z² = n·z` (χ₂'s was `1 − z² = az·z`).
* `emb : Qt n →+* ℝ`, `re + im√d ↦ re + im·Real.sqrt ((n/2)² − 1)`, with `emb (zK n) = zT n` (`Ti/Defs`).
* `0 < zT n < 1`, and `zT n ≤ zU 4 = √5 − 2` for `n ≥ 5` (`zT_le_zU_four`, for the shift lemma).
-/
import Chi2U.Ti.Defs

set_option linter.unusedSectionVars false

namespace Chi2U
namespace Ti

open QuadraticAlgebra

/-- `(n/2)² − 1` is not a rational square for `n ≥ 3` (it is one iff `n² − 4` is an integer square, and
`(n − 1)² < n² − 4 < n²`). -/
lemma not_isSquare_dT (n : ℕ) (hn : 3 ≤ n) : ¬ IsSquare (((n : ℚ) / 2) ^ 2 - 1) := by
  rintro ⟨q, hq⟩
  have h4 : 4 ≤ n ^ 2 := by nlinarith
  have h' : IsSquare (((n ^ 2 - 4 : ℕ)) : ℚ) := ⟨2 * q, by
    rw [Nat.cast_sub h4]; push_cast; linear_combination 4 * hq⟩
  rw [Rat.isSquare_natCast_iff] at h'
  obtain ⟨k, hk⟩ := h'
  have hk' : k * k + 4 = n ^ 2 := by omega
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have h1 : k < j + 1 := by
    by_contra hc
    push Not at hc
    have : (j + 1) * (j + 1) ≤ k * k := Nat.mul_le_mul hc hc
    nlinarith
  have h2 : j < k := by
    by_contra hc
    push Not at hc
    have : k * k ≤ j * j := Nat.mul_le_mul hc hc
    nlinarith
  omega

/-- `d = (n/2)² − 1` (a `def`, so that rewriting with `pow` lemmas never touches the type `Qt n`). -/
def dT (n : ℕ) : ℚ := ((n : ℚ) / 2) ^ 2 - 1

lemma dT_eq (n : ℕ) : dT n = ((n : ℚ) / 2) ^ 2 - 1 := rfl

/-- At even trace `n = 2m`: `d = m² − 1`. -/
lemma dT_two_mul (m : ℕ) : dT (2 * m) = (m : ℚ) ^ 2 - 1 := by unfold dT; push_cast; ring

lemma dT_pos (n : ℕ) [hn : Fact (3 ≤ n)] : 0 < dT n := by
  unfold dT
  have : (3 : ℚ) ≤ n := by exact_mod_cast hn.out
  nlinarith

lemma dT_ne_zero {n : ℕ} [Fact (3 ≤ n)] : dT n ≠ 0 := (dT_pos n).ne'

instance fact_not_isSquare_dT (n : ℕ) [hn : Fact (3 ≤ n)] : Fact (¬ IsSquare (dT n)) :=
  ⟨not_isSquare_dT n hn.out⟩

/-- `ℚ(√d)`, `d = (n/2)² − 1`, as `re + im·√d`. -/
abbrev Qt (n : ℕ) : Type := QuadraticAlgebra ℚ (dT n) 0

variable {n : ℕ} [Fact (3 ≤ n)]

lemma three_le : 3 ≤ n := Fact.out

/-- `√d ∈ Qt n`. -/
def sqrtd (n : ℕ) : Qt n := ⟨0, 1⟩

/-- The unit `z = n/2 − √d = (n − √(n² − 4))/2`. -/
def zK (n : ℕ) : Qt n := ⟨(n : ℚ) / 2, -1⟩

/-- The Galois conjugation `σ : √d ↦ −√d`. -/
def sig : Qt n →+* Qt n := starRingEnd (Qt n)

@[simp] lemma re_sig (x : Qt n) : (sig x).re = x.re := by simp [sig, starRingEnd_apply, re_star]

@[simp] lemma im_sig (x : Qt n) : (sig x).im = -x.im := by simp [sig, starRingEnd_apply, im_star]

lemma sig_sig (x : Qt n) : sig (sig x) = x := by ext <;> simp

lemma sig_ratCast (r : ℚ) : sig (r : Qt n) = r := by ext <;> simp

lemma sig_smul (r : ℚ) (x : Qt n) : sig (r • x) = r • sig x := by ext <;> simp

lemma sqrtd_mul_self : sqrtd n * sqrtd n = (dT n : Qt n) := by
  ext <;> simp [sqrtd]

lemma sig_sqrtd : sig (sqrtd n) = -sqrtd n := by ext <;> simp [sqrtd]

/-- `z⁻¹ = n/2 + √d`. -/
lemma zK_inv : (zK n)⁻¹ = ⟨(n : ℚ) / 2, 1⟩ :=
  inv_eq_of_mul_eq_one_right (by
    ext <;> simp only [zK, re_mul, im_mul, re_one, im_one] <;> (try rw [dT_eq]) <;> ring)

lemma zK_ne_zero : zK n ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.im h
  simp [zK] at this

lemma natCast_n_ne_zero : ((n : ℕ) : Qt n) ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.re h
  simp only [re_natCast, re_zero, Nat.cast_eq_zero] at this
  have := (Fact.out : 3 ≤ n); omega

lemma natCast_n_eq : ((n : ℕ) : Qt n) = ⟨(n : ℚ), 0⟩ := by ext <;> simp

/-- `z² − n·z + 1 = 0`. -/
lemma zK_sq_sub : zK n ^ 2 - (n : Qt n) * zK n + 1 = 0 := by
  rw [natCast_n_eq]
  ext <;> simp only [zK, sq, re_add, re_sub, re_mul, re_one, im_add, im_sub, im_mul, im_one, re_zero, im_zero] <;>
    (try rw [dT_eq]) <;> ring

/-- `1 + z² = n·z`. -/
lemma one_add_zK_sq : 1 + zK n ^ 2 = (n : Qt n) * zK n := by linear_combination (zK_sq_sub (n := n))

lemma one_add_zK_sq_ne_zero : (1 : Qt n) + zK n ^ 2 ≠ 0 := by
  rw [one_add_zK_sq]
  exact mul_ne_zero natCast_n_ne_zero zK_ne_zero

/-- `σz = z⁻¹` (norm `+1`). -/
lemma sig_zK : sig (zK n) = (zK n)⁻¹ := by
  rw [zK_inv]; ext <;> simp [zK]

lemma dT_real_nonneg : (0 : ℝ) ≤ ((n : ℝ) / 2) ^ 2 - 1 := by
  have : (3 : ℝ) ≤ n := by exact_mod_cast (Fact.out : 3 ≤ n)
  nlinarith

lemma sqrt_mul_self_dT :
    Real.sqrt (((n : ℝ) / 2) ^ 2 - 1) * Real.sqrt (((n : ℝ) / 2) ^ 2 - 1) = ((n : ℝ) / 2) ^ 2 - 1 :=
  Real.mul_self_sqrt dT_real_nonneg

/-- The real embedding `re + im√d ↦ re + im·√d`. -/
noncomputable def emb : Qt n →+* ℝ where
  toFun x := x.re + x.im * Real.sqrt (((n : ℝ) / 2) ^ 2 - 1)
  map_one' := by simp
  map_mul' x y := by
    simp only [re_mul, im_mul]
    push_cast
    simp only [dT_eq]
    push_cast
    have h5 := sqrt_mul_self_dT (n := n)
    linear_combination -(↑x.im * ↑y.im : ℝ) * h5
  map_zero' := by simp
  map_add' x y := by simp only [re_add, im_add]; push_cast; ring

lemma emb_apply (x : Qt n) : emb x = x.re + x.im * Real.sqrt (((n : ℝ) / 2) ^ 2 - 1) := rfl

lemma emb_zK : emb (zK n) = zT n := by simp [emb_apply, zK, zT]; ring

/-- `z_n · (n/2 + √d) = 1`. -/
lemma zT_mul : zT n * ((n : ℝ) / 2 + Real.sqrt (((n : ℝ) / 2) ^ 2 - 1)) = 1 := by
  unfold zT; linear_combination -(sqrt_mul_self_dT (n := n))

lemma zT_pos : 0 < zT n := by
  have h := zT_mul (n := n)
  have hs : 0 ≤ Real.sqrt (((n : ℝ) / 2) ^ 2 - 1) := Real.sqrt_nonneg _
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := (Fact.out : 3 ≤ n); omega)
  by_contra hc
  push Not at hc
  nlinarith

lemma zT_lt_one : zT n < 1 := by
  unfold zT
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast (Fact.out : 3 ≤ n)
  have : (n : ℝ) / 2 - 1 < Real.sqrt (((n : ℝ) / 2) ^ 2 - 1) :=
    (Real.lt_sqrt (by linarith)).mpr (by nlinarith)
  linarith

lemma zT_ne_zero : zT n ≠ 0 := zT_pos.ne'

/-- `z_n ≤ z₂ = √5 − 2` for `n ≥ 5` (PROOF_TI2 §2, Theorem B′_z and the shift lemma need `0 < z_n ≤ z₂`). -/
lemma zT_le_zU_four (hn5 : 5 ≤ n) : zT n ≤ zU 4 := by
  rw [zU_four]
  have h5 : (5 : ℝ) ≤ n := by exact_mod_cast hn5
  have hs5 : Real.sqrt 5 ≤ Real.sqrt (((n : ℝ) / 2) ^ 2 - 1) := Real.sqrt_le_sqrt (by nlinarith)
  have hmul := zT_mul (n := n)
  have hpos := zT_pos (n := n)
  have h55 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hsq : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  -- `zT n = 1/(n/2 + s) ≤ 1/(2 + √5) = √5 − 2`
  have key : zT n * (2 + Real.sqrt 5) ≤ 1 := by
    calc zT n * (2 + Real.sqrt 5) ≤ zT n * ((n : ℝ) / 2 + Real.sqrt (((n : ℝ) / 2) ^ 2 - 1)) := by
          gcongr; linarith
      _ = 1 := hmul
  nlinarith

lemma emb_comp_algebraMap : (emb (n := n)).comp (algebraMap ℚ (Qt n)) = algebraMap ℚ ℝ :=
  Subsingleton.elim _ _

end Ti
end Chi2U
