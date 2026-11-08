/-
# The field `ℚ(√d)`, `d = m² + 1`, the unit `z = √d − m`, and the real embedding

Parametrised by a natural number `mz` (the `m` of PROOF_V; named `mz` because `m` is the pole index throughout the
machine files) with `[Fact (1 ≤ mz)]`. Theorem U is `mz = 2` (`d = 5`, `z = √5 − 2`).

* `Qd mz := QuadraticAlgebra ℚ (mz² + 1) 0`: elements `re + im·√d`; a field (`mz² + 1` is not a square for
  `mz ≥ 1`: `not_isSquare_d`). `Q5 := Qd 2`.
* `sig`: the Galois conjugation `√d ↦ −√d` (Mathlib's `star` on `QuadraticAlgebra`), as a ring hom.
* `zK mz = √d − mz`: `z² + 2mz·z = 1`, `z⁻¹ = √d + mz`, `σz = −z⁻¹`, `1 − z² = 2mz·z`.
* `emb : Qd mz →+* ℝ`, `re + im√d ↦ re + im·Real.sqrt d`, with `emb (zK mz) = √d − mz = zU mz`.
-/
import Mathlib

set_option linter.unusedSectionVars false

namespace Chi2U

open QuadraticAlgebra

/-- `mz² + 1` is not a rational square for `mz ≥ 1`. -/
lemma not_isSquare_d (mz : ℕ) (hm : 1 ≤ mz) : ¬ IsSquare ((mz : ℚ) ^ 2 + 1) := by
  intro h
  have h' : IsSquare (((mz ^ 2 + 1 : ℕ)) : ℚ) := by push_cast; exact h
  rw [Rat.isSquare_natCast_iff] at h'
  obtain ⟨k, hk⟩ := h'
  have h1 : mz < k := by
    by_contra hc
    push Not at hc
    have : k * k ≤ mz * mz := Nat.mul_le_mul hc hc
    nlinarith
  have h2 : k < mz + 1 := by
    by_contra hc
    push Not at hc
    have : (mz + 1) * (mz + 1) ≤ k * k := Nat.mul_le_mul hc hc
    nlinarith
  omega

/-- `d = mz² + 1` (a `def`, so that rewriting with `pow` lemmas never touches the type `Qd mz`). -/
def dQ (mz : ℕ) : ℚ := (mz : ℚ) ^ 2 + 1

lemma dQ_eq (mz : ℕ) : dQ mz = (mz : ℚ) ^ 2 + 1 := rfl

lemma dQ_two : dQ 2 = 5 := by norm_num [dQ]

lemma dQ_pos (mz : ℕ) : 0 < dQ mz := by unfold dQ; positivity

lemma dQ_ne_zero {mz : ℕ} : dQ mz ≠ 0 := (dQ_pos mz).ne'

instance fact_not_isSquare_d (mz : ℕ) [hm : Fact (1 ≤ mz)] : Fact (¬ IsSquare (dQ mz)) :=
  ⟨not_isSquare_d mz hm.out⟩

instance fact_one_le_two : Fact (1 ≤ 2) := ⟨by norm_num⟩

/-- `ℚ(√d)`, `d = mz² + 1`, as `re + im·√d`. -/
abbrev Qd (mz : ℕ) : Type := QuadraticAlgebra ℚ (dQ mz) 0

/-- `ℚ(√5) = Qd 2` (Theorem U). -/
abbrev Q5 : Type := Qd 2

variable {mz : ℕ} [Fact (1 ≤ mz)]

/-- `√d ∈ Qd mz`. -/
def sqrtd (mz : ℕ) : Qd mz := ⟨0, 1⟩

/-- The unit `z = √d − mz` (`= φ⁻³` for `mz = 2`). -/
def zK (mz : ℕ) : Qd mz := ⟨-(mz : ℚ), 1⟩

/-- The Galois conjugation `σ : √d ↦ −√d`. -/
def sig : Qd mz →+* Qd mz := starRingEnd (Qd mz)

@[simp] lemma re_sig (x : Qd mz) : (sig x).re = x.re := by simp [sig, starRingEnd_apply, re_star]

@[simp] lemma im_sig (x : Qd mz) : (sig x).im = -x.im := by simp [sig, starRingEnd_apply, im_star]

lemma sig_sig (x : Qd mz) : sig (sig x) = x := by ext <;> simp

lemma sig_ratCast (r : ℚ) : sig (r : Qd mz) = r := by ext <;> simp

lemma sig_smul (r : ℚ) (x : Qd mz) : sig (r • x) = r • sig x := by ext <;> simp

lemma sqrtd_mul_self : sqrtd mz * sqrtd mz = (dQ mz : Qd mz) := by
  ext <;> simp [sqrtd]

lemma sig_sqrtd : sig (sqrtd mz) = -sqrtd mz := by ext <;> simp [sqrtd]

lemma zK_inv : (zK mz)⁻¹ = ⟨(mz : ℚ), 1⟩ :=
  inv_eq_of_mul_eq_one_right (by ext <;> simp [zK] <;> (try simp only [dQ_eq]) <;> ring)

lemma zK_ne_zero : zK mz ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.im h
  simp [zK] at this

lemma natCast_mz_ne_zero : ((mz : ℕ) : Qd mz) ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.re h
  simp only [re_natCast, re_zero, Nat.cast_eq_zero] at this
  have := (Fact.out : 1 ≤ mz); omega

lemma natCast_mz_eq : ((mz : ℕ) : Qd mz) = ⟨(mz : ℚ), 0⟩ := by ext <;> simp

lemma zK_sq_add : zK mz ^ 2 + 2 * (mz : Qd mz) * zK mz = 1 := by
  rw [natCast_mz_eq]; ext <;> simp [zK, sq] <;> (try simp only [dQ_eq]) <;> ring

/-- `1 − z² = 2mz·z`. -/
lemma one_sub_zK_sq : 1 - zK mz ^ 2 = 2 * (mz : Qd mz) * zK mz := by linear_combination -(zK_sq_add (mz := mz))

lemma one_sub_zK_sq_ne_zero : (1 : Qd mz) - zK mz ^ 2 ≠ 0 := by
  rw [one_sub_zK_sq]
  exact mul_ne_zero (mul_ne_zero two_ne_zero natCast_mz_ne_zero) zK_ne_zero

lemma sig_zK : sig (zK mz) = -(zK mz)⁻¹ := by
  rw [zK_inv]; ext <;> simp [zK]

/-- The real embedding `re + im√d ↦ re + im·√d`. -/
noncomputable def emb : Qd mz →+* ℝ where
  toFun x := x.re + x.im * Real.sqrt ((mz : ℝ) ^ 2 + 1)
  map_one' := by simp
  map_mul' x y := by
    simp only [re_mul, im_mul]
    push_cast
    simp only [dQ_eq]
    push_cast
    have h5 : Real.sqrt ((mz : ℝ) ^ 2 + 1) * Real.sqrt ((mz : ℝ) ^ 2 + 1) = (mz : ℝ) ^ 2 + 1 :=
      Real.mul_self_sqrt (by positivity)
    linear_combination -(↑x.im * ↑y.im : ℝ) * h5
  map_zero' := by simp
  map_add' x y := by simp only [re_add, im_add]; push_cast; ring

lemma emb_apply (x : Qd mz) : emb x = x.re + x.im * Real.sqrt ((mz : ℝ) ^ 2 + 1) := rfl

/-- `z = √(mz² + 1) − mz` as a real number. -/
noncomputable def zU (mz : ℕ) : ℝ := Real.sqrt ((mz : ℝ) ^ 2 + 1) - mz

lemma emb_zK : emb (zK mz) = zU mz := by simp [emb_apply, zK, zU]; ring

lemma zU_two : zU 2 = Real.sqrt 5 - 2 := by unfold zU; norm_num

lemma zU_pos : 0 < zU mz := by
  unfold zU
  have : (mz : ℝ) < Real.sqrt ((mz : ℝ) ^ 2 + 1) :=
    (Real.lt_sqrt (by positivity)).mpr (by linarith)
  linarith

lemma zU_lt_one : zU mz < 1 := by
  unfold zU
  have hm : (1 : ℝ) ≤ mz := by exact_mod_cast (Fact.out : 1 ≤ mz)
  have : Real.sqrt ((mz : ℝ) ^ 2 + 1) < mz + 1 :=
    (Real.sqrt_lt' (by positivity)).mpr (by nlinarith)
  linarith

lemma emb_comp_algebraMap : (emb (mz := mz)).comp (algebraMap ℚ (Qd mz)) = algebraMap ℚ ℝ :=
  Subsingleton.elim _ _

end Chi2U
