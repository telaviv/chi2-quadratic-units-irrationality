/-
# The field `ℚ(√d)`, `d = (a/2)² + 1`, the unit `z = √d − a/2`, and the real embedding

Parametrised by the **trace** `az : ℕ` (the `a` of PROOF_VODD: `z = (√(a² + 4) − a)/2`, `z⁻¹ − z = a`, i.e. the
trace of `z⁻¹`; `a = 2m` in PROOF_V, `a = 4` for Theorem U) with `[Fact (1 ≤ az)]`. Theorem U is
`az = 4` (`d = 5`, `z = √5 − 2`); Theorem V is `az = 2m` (`d = m² + 1`, `z = √(m² + 1) − m`).

* `Qd az := QuadraticAlgebra ℚ ((az/2)² + 1) 0`: elements `re + im·√d`; a field (`(a/2)² + 1` is not a square for
  `a ≥ 1`: `not_isSquare_d`). `Q5 := Qd 4`.
* `sig`: the Galois conjugation `√d ↦ −√d` (Mathlib's `star` on `QuadraticAlgebra`), as a ring hom.
* `zK az = √d − a/2`: `z² + a·z = 1`, `z⁻¹ = √d + a/2`, `σz = −z⁻¹`, `1 − z² = a·z`.
* `emb : Qd az →+* ℝ`, `re + im√d ↦ re + im·Real.sqrt d`, with `emb (zK az) = √d − a/2 = zU az`.
-/
import Mathlib

set_option linter.unusedSectionVars false

namespace Chi2U

open QuadraticAlgebra

/-- `(az/2)² + 1` is not a rational square for `az ≥ 1` (it is one iff `az² + 4` is an integer square iff
`az = 0`). -/
lemma not_isSquare_d (az : ℕ) (ha : 1 ≤ az) : ¬ IsSquare (((az : ℚ) / 2) ^ 2 + 1) := by
  rintro ⟨q, hq⟩
  have h' : IsSquare (((az ^ 2 + 4 : ℕ)) : ℚ) := ⟨2 * q, by push_cast; linear_combination 4 * hq⟩
  rw [Rat.isSquare_natCast_iff] at h'
  obtain ⟨k, hk⟩ := h'
  have h1 : az < k := by
    by_contra hc
    push Not at hc
    have : k * k ≤ az * az := Nat.mul_le_mul hc hc
    nlinarith
  have h2 : k < az + 2 := by
    by_contra hc
    push Not at hc
    have : (az + 2) * (az + 2) ≤ k * k := Nat.mul_le_mul hc hc
    nlinarith
  have hk1 : k = az + 1 := by omega
  subst hk1
  ring_nf at hk
  omega

/-- `d = (az/2)² + 1` (a `def`, so that rewriting with `pow` lemmas never touches the type `Qd az`). -/
def dQ (az : ℕ) : ℚ := ((az : ℚ) / 2) ^ 2 + 1

lemma dQ_eq (az : ℕ) : dQ az = ((az : ℚ) / 2) ^ 2 + 1 := rfl

lemma dQ_four : dQ 4 = 5 := by norm_num [dQ]

/-- At even trace `az = 2m`: `d = m² + 1`. -/
lemma dQ_two_mul (m : ℕ) : dQ (2 * m) = (m : ℚ) ^ 2 + 1 := by unfold dQ; push_cast; ring

lemma dQ_pos (az : ℕ) : 0 < dQ az := by unfold dQ; positivity

lemma dQ_ne_zero {az : ℕ} : dQ az ≠ 0 := (dQ_pos az).ne'

instance fact_not_isSquare_d (az : ℕ) [ha : Fact (1 ≤ az)] : Fact (¬ IsSquare (dQ az)) :=
  ⟨not_isSquare_d az ha.out⟩

instance fact_one_le_four : Fact (1 ≤ 4) := ⟨by norm_num⟩

/-- `1 ≤ 2m` from `1 ≤ m` (Theorem V instantiates the trace `az := 2 * m`). -/
instance fact_one_le_two_mul (m : ℕ) [hm : Fact (1 ≤ m)] : Fact (1 ≤ 2 * m) := ⟨by have := hm.out; omega⟩

/-- `ℚ(√d)`, `d = (az/2)² + 1`, as `re + im·√d`. -/
abbrev Qd (az : ℕ) : Type := QuadraticAlgebra ℚ (dQ az) 0

/-- `ℚ(√5) = Qd 4` (Theorem U). -/
abbrev Q5 : Type := Qd 4

variable {az : ℕ} [Fact (1 ≤ az)]

/-- `√d ∈ Qd az`. -/
def sqrtd (az : ℕ) : Qd az := ⟨0, 1⟩

/-- The unit `z = √d − az/2 = (√(az² + 4) − az)/2` (`= φ⁻³` for `az = 4`). -/
def zK (az : ℕ) : Qd az := ⟨-(az : ℚ) / 2, 1⟩

/-- The Galois conjugation `σ : √d ↦ −√d`. -/
def sig : Qd az →+* Qd az := starRingEnd (Qd az)

@[simp] lemma re_sig (x : Qd az) : (sig x).re = x.re := by simp [sig, starRingEnd_apply, re_star]

@[simp] lemma im_sig (x : Qd az) : (sig x).im = -x.im := by simp [sig, starRingEnd_apply, im_star]

lemma sig_sig (x : Qd az) : sig (sig x) = x := by ext <;> simp

lemma sig_ratCast (r : ℚ) : sig (r : Qd az) = r := by ext <;> simp

lemma sig_smul (r : ℚ) (x : Qd az) : sig (r • x) = r • sig x := by ext <;> simp

lemma sqrtd_mul_self : sqrtd az * sqrtd az = (dQ az : Qd az) := by
  ext <;> simp [sqrtd]

lemma sig_sqrtd : sig (sqrtd az) = -sqrtd az := by ext <;> simp [sqrtd]

lemma zK_inv : (zK az)⁻¹ = ⟨(az : ℚ) / 2, 1⟩ :=
  inv_eq_of_mul_eq_one_right (by ext <;> simp [zK] <;> (try simp only [dQ_eq]) <;> ring)

lemma zK_ne_zero : zK az ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.im h
  simp [zK] at this

lemma natCast_az_ne_zero : ((az : ℕ) : Qd az) ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.re h
  simp only [re_natCast, re_zero, Nat.cast_eq_zero] at this
  have := (Fact.out : 1 ≤ az); omega

lemma natCast_az_eq : ((az : ℕ) : Qd az) = ⟨(az : ℚ), 0⟩ := by ext <;> simp

/-- `z² + az·z = 1`. -/
lemma zK_sq_add : zK az ^ 2 + (az : Qd az) * zK az = 1 := by
  rw [natCast_az_eq]; ext <;> simp [zK, sq] <;> (try simp only [dQ_eq]) <;> ring

/-- `1 − z² = az·z`. -/
lemma one_sub_zK_sq : 1 - zK az ^ 2 = (az : Qd az) * zK az := by linear_combination -(zK_sq_add (az := az))

lemma one_sub_zK_sq_ne_zero : (1 : Qd az) - zK az ^ 2 ≠ 0 := by
  rw [one_sub_zK_sq]
  exact mul_ne_zero natCast_az_ne_zero zK_ne_zero

lemma sig_zK : sig (zK az) = -(zK az)⁻¹ := by
  rw [zK_inv]; ext <;> simp [zK] <;> ring

/-- The real embedding `re + im√d ↦ re + im·√d`. -/
noncomputable def emb : Qd az →+* ℝ where
  toFun x := x.re + x.im * Real.sqrt (((az : ℝ) / 2) ^ 2 + 1)
  map_one' := by simp
  map_mul' x y := by
    simp only [re_mul, im_mul]
    push_cast
    simp only [dQ_eq]
    push_cast
    have h5 : Real.sqrt (((az : ℝ) / 2) ^ 2 + 1) * Real.sqrt (((az : ℝ) / 2) ^ 2 + 1) = ((az : ℝ) / 2) ^ 2 + 1 :=
      Real.mul_self_sqrt (by positivity)
    linear_combination -(↑x.im * ↑y.im : ℝ) * h5
  map_zero' := by simp
  map_add' x y := by simp only [re_add, im_add]; push_cast; ring

lemma emb_apply (x : Qd az) : emb x = x.re + x.im * Real.sqrt (((az : ℝ) / 2) ^ 2 + 1) := rfl

/-- `z = √((az/2)² + 1) − az/2` as a real number. -/
noncomputable def zU (az : ℕ) : ℝ := Real.sqrt (((az : ℝ) / 2) ^ 2 + 1) - az / 2

lemma emb_zK : emb (zK az) = zU az := by simp [emb_apply, zK, zU]; ring

lemma zU_four : zU 4 = Real.sqrt 5 - 2 := by unfold zU; norm_num

/-- At even trace `az = 2m`: `z = √(m² + 1) − m` (Theorem V). -/
lemma zU_two_mul (m : ℕ) : zU (2 * m) = Real.sqrt ((m : ℝ) ^ 2 + 1) - m := by
  unfold zU; push_cast; ring_nf

lemma zU_pos : 0 < zU az := by
  unfold zU
  have : (az : ℝ) / 2 < Real.sqrt (((az : ℝ) / 2) ^ 2 + 1) :=
    (Real.lt_sqrt (by positivity)).mpr (by linarith)
  linarith

lemma zU_lt_one : zU az < 1 := by
  unfold zU
  have ha : (1 : ℝ) ≤ az := by exact_mod_cast (Fact.out : 1 ≤ az)
  have : Real.sqrt (((az : ℝ) / 2) ^ 2 + 1) < az / 2 + 1 :=
    (Real.sqrt_lt' (by positivity)).mpr (by nlinarith)
  linarith

lemma emb_comp_algebraMap : (emb (az := az)).comp (algebraMap ℚ (Qd az)) = algebraMap ℚ ℝ :=
  Subsingleton.elim _ _

end Chi2U
