/-
# The field ℚ(√5), the unit `z = √5 − 2`, and the real embedding

* `Q5 := QuadraticAlgebra ℚ 5 0`: elements `re + im·√5`; a field (`5` is not a square in `ℚ`).
* `sig`: the Galois conjugation `√5 ↦ −√5` (Mathlib's `star` on `QuadraticAlgebra`), as a ring hom.
* `zK = √5 − 2`: `z² + 4z = 1`, `z⁻¹ = √5 + 2`, `σz = −z⁻¹`, `1 − z² = 4z`.
* `emb : Q5 →+* ℝ`, `re + im√5 ↦ re + im·Real.sqrt 5`, with `emb zK = √5 − 2 = zU`.
-/
import Mathlib

namespace Chi2U

open QuadraticAlgebra

lemma not_isSquare_five : ¬ IsSquare (5 : ℚ) := by
  rintro ⟨r, hr⟩
  have h5 : Irrational (Real.sqrt 5) := by
    have : Nat.Prime 5 := by norm_num
    exact_mod_cast this.irrational_sqrt
  apply h5
  refine ⟨|r|, ?_⟩
  have hr' : ((5 : ℚ) : ℝ) = (r : ℝ) * r := by exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) hr
  push_cast at hr' ⊢
  rw [hr', Real.sqrt_mul_self_eq_abs]

instance fact_not_isSquare_five : Fact (¬ IsSquare (5 : ℚ)) := ⟨not_isSquare_five⟩

/-- `ℚ(√5)`, as `re + im·√5`. -/
abbrev Q5 : Type := QuadraticAlgebra ℚ 5 0

/-- `√5 ∈ Q5`. -/
def sqrt5 : Q5 := ⟨0, 1⟩

/-- The unit `z = √5 − 2 = φ⁻³`. -/
def zK : Q5 := ⟨-2, 1⟩

/-- The Galois conjugation `σ : √5 ↦ −√5`. -/
def sig : Q5 →+* Q5 := starRingEnd Q5

@[simp] lemma re_sig (x : Q5) : (sig x).re = x.re := by simp [sig, starRingEnd_apply, re_star]

@[simp] lemma im_sig (x : Q5) : (sig x).im = -x.im := by simp [sig, starRingEnd_apply, im_star]

lemma sig_sig (x : Q5) : sig (sig x) = x := by ext <;> simp

lemma sig_ratCast (r : ℚ) : sig (r : Q5) = r := by ext <;> simp

lemma sig_smul (r : ℚ) (x : Q5) : sig (r • x) = r • sig x := by ext <;> simp

lemma sqrt5_mul_self : sqrt5 * sqrt5 = 5 := by ext <;> simp [sqrt5]

lemma sig_sqrt5 : sig sqrt5 = -sqrt5 := by ext <;> simp [sqrt5]

lemma zK_inv : zK⁻¹ = ⟨2, 1⟩ :=
  inv_eq_of_mul_eq_one_right (by ext <;> simp [zK] <;> norm_num)

lemma zK_ne_zero : zK ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.im h
  simp [zK] at this

lemma zK_sq_add : zK ^ 2 + 4 * zK = 1 := by ext <;> simp [zK, sq] <;> norm_num

/-- `1 − z² = 4z`. -/
lemma one_sub_zK_sq : 1 - zK ^ 2 = 4 * zK := by linear_combination -zK_sq_add

lemma one_sub_zK_sq_ne_zero : (1 : Q5) - zK ^ 2 ≠ 0 := by
  rw [one_sub_zK_sq]
  exact mul_ne_zero (by norm_num) zK_ne_zero

lemma sig_zK : sig zK = -zK⁻¹ := by
  rw [zK_inv]; ext <;> simp [zK]

/-- The real embedding `re + im√5 ↦ re + im·√5`. -/
noncomputable def emb : Q5 →+* ℝ where
  toFun x := x.re + x.im * Real.sqrt 5
  map_one' := by simp
  map_mul' x y := by
    simp only [re_mul, im_mul]
    push_cast
    have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
    linear_combination -(↑x.im * ↑y.im : ℝ) * h5
  map_zero' := by simp
  map_add' x y := by simp only [re_add, im_add]; push_cast; ring

lemma emb_apply (x : Q5) : emb x = x.re + x.im * Real.sqrt 5 := rfl

/-- `z = √5 − 2` as a real number. -/
noncomputable def zU : ℝ := Real.sqrt 5 - 2

lemma emb_zK : emb zK = zU := by simp [emb_apply, zK, zU]; ring

lemma zU_pos : 0 < zU := by
  unfold zU
  have : (2 : ℝ) < Real.sqrt 5 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

lemma zU_lt_one : zU < 1 := by
  unfold zU
  have : Real.sqrt 5 < 3 := by
    rw [show (3 : ℝ) = Real.sqrt 9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

lemma emb_comp_algebraMap : emb.comp (algebraMap ℚ Q5) = algebraMap ℚ ℝ := Subsingleton.elim _ _

end Chi2U
