/-
# The odd moments `S_n = Σ_{t odd ≥ 1} z^t t^n` and their parity

`Smom mz n ∈ ℚ(√d)` (all parametrised by `mz` with `[Fact (1 ≤ mz)]`, `d = mz² + 1`; Theorem U is `mz = 2`) is defined by the recurrence obtained from
`t^n − (t−2)^n` and `1 − z² = 2mz·z ≠ 0`:

    (1 − z²) S_n = (−1)^n z − Σ_{k<n} C(n,k) (−2)^{n−k} S_k.

`Lmom : ℚ[X] →ₗ[ℚ] Q5` is the moment functional `X^n ↦ S_n` (so `Lmom p = Σ_{t odd ≥ 1} z^t p(t)`;
the series identity is `PoleExpansion.hasSum_Smom`). It satisfies
* (rec₁) `Lmom (p(t − 2)) − z² Lmom p = z·p(−1)`,
* (rec₂) `z² Lmom (q(t + 2)) = Lmom q − z·q(1)`,
and **parity**: `σ(Lmom p) = Lmom (p(−t))`, i.e. `σ S_n = (−1)^n S_n` (`sig_Lmom`).
Proof of parity: `p ↦ σ(Lmom(p(−t)))` also satisfies rec₁ (by rec₂ and `σz = −z⁻¹`), and rec₁ has a unique solution.

`muPoly R := Lmom R′` is `μ(R) = Σ_{t odd ≥ 1} z^t R′(t)`; `σ μ(R) = −μ(R(−t))` (`sig_muPoly`).
-/
import Chi2U.Field

namespace Chi2U

variable {mz : ℕ} [Fact (1 ≤ mz)]

open Polynomial

/-- `S_n = Σ_{t odd ≥ 1} z^t t^n`, via the recurrence. -/
noncomputable def Smom (mz : ℕ) [Fact (1 ≤ mz)] : ℕ → (Qd mz)
  | n => ((-1) ^ n * (zK mz) - ∑ k : Fin n, ((n.choose k : ℕ) : (Qd mz)) * (-2) ^ (n - (k : ℕ)) * Smom mz k) / (1 - (zK mz) ^ 2)
termination_by n => n
decreasing_by exact k.isLt

lemma Smom_rec (n : ℕ) :
    (1 - (zK mz) ^ 2) * Smom mz n = (-1) ^ n * (zK mz) - ∑ k ∈ Finset.range n, ((n.choose k : ℕ) : (Qd mz)) * (-2) ^ (n - k) * Smom mz k := by
  rw [Smom, mul_div_cancel₀ _ one_sub_zK_sq_ne_zero, Finset.sum_range (fun k => ((n.choose k : ℕ) : (Qd mz)) * (-2) ^ (n - k) * Smom mz k)]

/-- The moment functional `X^n ↦ S_n`. -/
noncomputable def Lmom (mz : ℕ) [Fact (1 ≤ mz)] : ℚ[X] →ₗ[ℚ] (Qd mz) := Polynomial.lsum (fun n => LinearMap.toSpanSingleton ℚ (Qd mz) (Smom mz n))

lemma Lmom_monomial (n : ℕ) (c : ℚ) : Lmom mz (monomial n c) = c • Smom mz n := by
  simp [Lmom]

lemma Lmom_X_pow (n : ℕ) : Lmom mz (X ^ n) = Smom mz n := by
  rw [← monomial_one_right_eq_X_pow, Lmom_monomial, one_smul]

lemma Lmom_C_mul (c : ℚ) (p : ℚ[X]) : Lmom mz (C c * p) = c • Lmom mz p := by
  rw [← smul_eq_C_mul, map_smul]

/-- `(t − 2)^n = Σ_{k ≤ n} C(n,k) (−2)^{n−k} t^k`. -/
lemma X_sub_two_pow (n : ℕ) :
    (X - C 2 : ℚ[X]) ^ n = ∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℚ) * (-2) ^ (n - k)) * X ^ k := by
  rw [sub_eq_add_neg, add_pow]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [C_mul, C_pow, C_neg, map_natCast]
  ring

lemma Lmom_X_sub_two_pow {L : ℚ[X] →ₗ[ℚ] (Qd mz)} (n : ℕ) :
    L ((X - C 2) ^ n) = ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℕ) : (Qd mz)) * (-2) ^ (n - k) * L (X ^ k) := by
  rw [X_sub_two_pow, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← smul_eq_C_mul, map_smul]
  rw [Algebra.smul_def]
  simp

/-- (rec₁) `Lmom(p(t−2)) − z² Lmom(p) = z p(−1)`. -/
lemma Lmom_rec1 (p : ℚ[X]) :
    Lmom mz (p.comp (X - C 2)) - (zK mz) ^ 2 * Lmom mz p = (zK mz) * ((p.eval (-1) : ℚ) : (Qd mz)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [add_comp, map_add, map_add, eval_add]; push_cast; linear_combination hp + hq
  | monomial n c =>
      rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, Lmom_C_mul, Lmom_C_mul,
        Lmom_X_sub_two_pow, Lmom_X_pow, Finset.sum_range_succ]
      simp only [Lmom_X_pow, Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, one_mul, eval_mul, eval_C,
        eval_pow, eval_X]
      have hrec := Smom_rec (mz := mz) n
      simp only [Algebra.smul_def, eq_ratCast]
      push_cast
      linear_combination (c : (Qd mz)) * hrec

/-- (rec₂) `z² Lmom(q(t+2)) = Lmom q − z q(1)`. -/
lemma Lmom_rec2 (q : ℚ[X]) :
    (zK mz) ^ 2 * Lmom mz (q.comp (X + C 2)) = Lmom mz q - (zK mz) * ((q.eval 1 : ℚ) : (Qd mz)) := by
  have h := Lmom_rec1 (mz := mz) (q.comp (X + C 2))
  rw [comp_assoc, show (X + C 2 : ℚ[X]).comp (X - C 2) = X by simp, comp_X, eval_comp] at h
  simp only [eval_add, eval_X, eval_C] at h
  norm_num at h
  linear_combination -h

/-- rec₁ determines the functional: two solutions agree. -/
lemma eq_Lmom_of_rec1 (L : ℚ[X] →ₗ[ℚ] (Qd mz))
    (hL : ∀ p : ℚ[X], L (p.comp (X - C 2)) - (zK mz) ^ 2 * L p = (zK mz) * ((p.eval (-1) : ℚ) : (Qd mz))) : L = Lmom mz := by
  set Δ := L - Lmom mz with hΔ
  have hhom : ∀ p : ℚ[X], Δ (p.comp (X - C 2)) = (zK mz) ^ 2 * Δ p := by
    intro p
    have h1 := hL p
    have h2 := Lmom_rec1 (mz := mz) p
    simp only [hΔ, LinearMap.sub_apply]
    linear_combination h1 - h2
  have hX : ∀ n, Δ (X ^ n) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have h := hhom (X ^ n)
      rw [X_pow_comp, Lmom_X_sub_two_pow, Finset.sum_range_succ,
        Finset.sum_eq_zero (fun k hk => by rw [ih k (Finset.mem_range.mp hk), mul_zero])] at h
      simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, one_mul, zero_add] at h
      have h' : (1 - (zK mz) ^ 2) * Δ (X ^ n) = 0 := by linear_combination h
      exact (mul_eq_zero.mp h').resolve_left one_sub_zK_sq_ne_zero
  have : Δ = 0 := by
    refine Polynomial.lhom_ext' (fun n => LinearMap.ext_ring ?_)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, monomial_one_right_eq_X_pow]
    exact hX n
  rw [hΔ, sub_eq_zero] at this
  exact this

/-- `p ↦ σ(Lmom(p(−t)))` as a `ℚ`-linear map. -/
noncomputable def LmomRefl (mz : ℕ) [Fact (1 ≤ mz)] : ℚ[X] →ₗ[ℚ] (Qd mz) where
  toFun p := sig (Lmom mz (p.comp (-X)))
  map_add' p q := by rw [add_comp, map_add, map_add]
  map_smul' c p := by
    rw [smul_comp, map_smul, sig_smul]; rfl

lemma LmomRefl_eq : LmomRefl mz = Lmom mz := by
  apply eq_Lmom_of_rec1
  intro p
  show sig (Lmom mz ((p.comp (X - C 2)).comp (-X))) - (zK mz) ^ 2 * sig (Lmom mz (p.comp (-X))) =
    (zK mz) * ((p.eval (-1) : ℚ) : (Qd mz))
  have hlin : (X - C 2 : ℚ[X]).comp (-X) = (-X).comp (X + C 2) := by
    simp only [sub_comp, X_comp, C_comp, neg_comp]; ring
  have hcomp : (p.comp (X - C 2)).comp (-X) = (p.comp (-X)).comp (X + C 2) := by
    rw [comp_assoc, comp_assoc, hlin]
  rw [hcomp]
  have h2 := congrArg sig (Lmom_rec2 (mz := mz) (p.comp (-X)))
  simp only [map_mul, map_sub, map_pow, sig_zK, sig_ratCast, eval_comp, eval_neg, eval_X] at h2
  have hz := zK_ne_zero (mz := mz)
  have hzi : (zK mz) * (zK mz)⁻¹ = 1 := mul_inv_cancel₀ hz
  have key : sig (Lmom mz ((p.comp (-X)).comp (X + C 2))) =
      (zK mz) ^ 2 * sig (Lmom mz (p.comp (-X))) + (zK mz) * ((p.eval (-1) : ℚ) : (Qd mz)) := by
    linear_combination (zK mz) ^ 2 * h2 + ((zK mz) * ((p.eval (-1) : ℚ) : (Qd mz)) -
      (1 + (zK mz) * (zK mz)⁻¹) * sig (Lmom mz ((p.comp (-X)).comp (X + C 2)))) * hzi
  rw [key]; ring

/-- **Parity of the moments**: `σ(Lmom p) = Lmom(p(−t))`. -/
theorem sig_Lmom (p : ℚ[X]) : sig (Lmom mz p) = Lmom mz (p.comp (-X)) := by
  have h := congrArg (fun L : ℚ[X] →ₗ[ℚ] (Qd mz) => L (p.comp (-X))) LmomRefl_eq
  simp only [LmomRefl, LinearMap.coe_mk, AddHom.coe_mk, comp_assoc, neg_comp, X_comp, neg_neg, comp_X] at h
  exact h

/-- `σ S_n = (−1)^n S_n`. -/
theorem sig_Smom (n : ℕ) : sig (Smom mz n) = (-1) ^ n * Smom mz n := by
  rw [← Lmom_X_pow, sig_Lmom, X_pow_comp, neg_pow, ← C_1, ← C_neg, ← C_pow, Lmom_C_mul, Algebra.smul_def]
  simp

/-- `μ(R) = Σ_{t odd ≥ 1} z^t R′(t) = Lmom(R′)` on polynomials. -/
noncomputable def muPoly (mz : ℕ) [Fact (1 ≤ mz)] (R : ℚ[X]) : (Qd mz) := Lmom mz (derivative R)

lemma muPoly_add (R S : ℚ[X]) : muPoly mz (R + S) = muPoly mz R + muPoly mz S := by
  simp [muPoly, map_add]

lemma muPoly_smul (c : ℚ) (R : ℚ[X]) : muPoly mz (c • R) = c • muPoly mz R := by
  simp [muPoly, map_smul]

/-- `σ μ(R) = −μ(R(−t))`. -/
theorem sig_muPoly (R : ℚ[X]) : sig (muPoly mz R) = -muPoly mz (R.comp (-X)) := by
  unfold muPoly
  rw [sig_Lmom, derivative_comp, derivative_neg, derivative_X]
  rw [show (-1 : ℚ[X]) * (derivative R).comp (-X) = (-1 : ℚ) • (derivative R).comp (-X) by
    rw [Algebra.smul_def]; simp]
  rw [map_smul]; simp

end Chi2U
