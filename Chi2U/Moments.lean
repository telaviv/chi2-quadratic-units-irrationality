/-
# The odd moments `S_n = Σ_{t odd ≥ 1} z^t t^n` and their parity

`Smom az n ∈ ℚ(√d)` (all parametrised by `az` with `[Fact (1 ≤ az)]`, `d = (az/2)² + 1`; Theorem U is `az = 4`) is defined by the recurrence obtained from
`t^n − (t−2)^n` and `1 − z² = az·z ≠ 0`:

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

variable {az : ℕ} [Fact (1 ≤ az)]

open Polynomial

/-- `S_n = Σ_{t odd ≥ 1} z^t t^n`, via the recurrence. -/
noncomputable def Smom (az : ℕ) [Fact (1 ≤ az)] : ℕ → (Qd az)
  | n => ((-1) ^ n * (zK az) - ∑ k : Fin n, ((n.choose k : ℕ) : (Qd az)) * (-2) ^ (n - (k : ℕ)) * Smom az k) / (1 - (zK az) ^ 2)
termination_by n => n
decreasing_by exact k.isLt

lemma Smom_rec (n : ℕ) :
    (1 - (zK az) ^ 2) * Smom az n = (-1) ^ n * (zK az) - ∑ k ∈ Finset.range n, ((n.choose k : ℕ) : (Qd az)) * (-2) ^ (n - k) * Smom az k := by
  rw [Smom, mul_div_cancel₀ _ one_sub_zK_sq_ne_zero, Finset.sum_range (fun k => ((n.choose k : ℕ) : (Qd az)) * (-2) ^ (n - k) * Smom az k)]

/-- The moment functional `X^n ↦ S_n`. -/
noncomputable def Lmom (az : ℕ) [Fact (1 ≤ az)] : ℚ[X] →ₗ[ℚ] (Qd az) := Polynomial.lsum (fun n => LinearMap.toSpanSingleton ℚ (Qd az) (Smom az n))

lemma Lmom_monomial (n : ℕ) (c : ℚ) : Lmom az (monomial n c) = c • Smom az n := by
  simp [Lmom]

lemma Lmom_X_pow (n : ℕ) : Lmom az (X ^ n) = Smom az n := by
  rw [← monomial_one_right_eq_X_pow, Lmom_monomial, one_smul]

lemma Lmom_C_mul (c : ℚ) (p : ℚ[X]) : Lmom az (C c * p) = c • Lmom az p := by
  rw [← smul_eq_C_mul, map_smul]

/-- `(t − 2)^n = Σ_{k ≤ n} C(n,k) (−2)^{n−k} t^k`. -/
lemma X_sub_two_pow (n : ℕ) :
    (X - C 2 : ℚ[X]) ^ n = ∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℚ) * (-2) ^ (n - k)) * X ^ k := by
  rw [sub_eq_add_neg, add_pow]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [C_mul, C_pow, C_neg, map_natCast]
  ring

lemma Lmom_X_sub_two_pow {L : ℚ[X] →ₗ[ℚ] (Qd az)} (n : ℕ) :
    L ((X - C 2) ^ n) = ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℕ) : (Qd az)) * (-2) ^ (n - k) * L (X ^ k) := by
  rw [X_sub_two_pow, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← smul_eq_C_mul, map_smul]
  rw [Algebra.smul_def]
  simp

/-- (rec₁) `Lmom(p(t−2)) − z² Lmom(p) = z p(−1)`. -/
lemma Lmom_rec1 (p : ℚ[X]) :
    Lmom az (p.comp (X - C 2)) - (zK az) ^ 2 * Lmom az p = (zK az) * ((p.eval (-1) : ℚ) : (Qd az)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [add_comp, map_add, map_add, eval_add]; push_cast; linear_combination hp + hq
  | monomial n c =>
      rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, Lmom_C_mul, Lmom_C_mul,
        Lmom_X_sub_two_pow, Lmom_X_pow, Finset.sum_range_succ]
      simp only [Lmom_X_pow, Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, one_mul, eval_mul, eval_C,
        eval_pow, eval_X]
      have hrec := Smom_rec (az := az) n
      simp only [Algebra.smul_def, eq_ratCast]
      push_cast
      linear_combination (c : (Qd az)) * hrec

/-- (rec₂) `z² Lmom(q(t+2)) = Lmom q − z q(1)`. -/
lemma Lmom_rec2 (q : ℚ[X]) :
    (zK az) ^ 2 * Lmom az (q.comp (X + C 2)) = Lmom az q - (zK az) * ((q.eval 1 : ℚ) : (Qd az)) := by
  have h := Lmom_rec1 (az := az) (q.comp (X + C 2))
  rw [comp_assoc, show (X + C 2 : ℚ[X]).comp (X - C 2) = X by simp, comp_X, eval_comp] at h
  simp only [eval_add, eval_X, eval_C] at h
  norm_num at h
  linear_combination -h

/-- rec₁ determines the functional: two solutions agree. -/
lemma eq_Lmom_of_rec1 (L : ℚ[X] →ₗ[ℚ] (Qd az))
    (hL : ∀ p : ℚ[X], L (p.comp (X - C 2)) - (zK az) ^ 2 * L p = (zK az) * ((p.eval (-1) : ℚ) : (Qd az))) : L = Lmom az := by
  set Δ := L - Lmom az with hΔ
  have hhom : ∀ p : ℚ[X], Δ (p.comp (X - C 2)) = (zK az) ^ 2 * Δ p := by
    intro p
    have h1 := hL p
    have h2 := Lmom_rec1 (az := az) p
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
      have h' : (1 - (zK az) ^ 2) * Δ (X ^ n) = 0 := by linear_combination h
      exact (mul_eq_zero.mp h').resolve_left one_sub_zK_sq_ne_zero
  have : Δ = 0 := by
    refine Polynomial.lhom_ext' (fun n => LinearMap.ext_ring ?_)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, monomial_one_right_eq_X_pow]
    exact hX n
  rw [hΔ, sub_eq_zero] at this
  exact this

/-- `p ↦ σ(Lmom(p(−t)))` as a `ℚ`-linear map. -/
noncomputable def LmomRefl (az : ℕ) [Fact (1 ≤ az)] : ℚ[X] →ₗ[ℚ] (Qd az) where
  toFun p := sig (Lmom az (p.comp (-X)))
  map_add' p q := by rw [add_comp, map_add, map_add]
  map_smul' c p := by
    rw [smul_comp, map_smul, sig_smul]; rfl

lemma LmomRefl_eq : LmomRefl az = Lmom az := by
  apply eq_Lmom_of_rec1
  intro p
  show sig (Lmom az ((p.comp (X - C 2)).comp (-X))) - (zK az) ^ 2 * sig (Lmom az (p.comp (-X))) =
    (zK az) * ((p.eval (-1) : ℚ) : (Qd az))
  have hlin : (X - C 2 : ℚ[X]).comp (-X) = (-X).comp (X + C 2) := by
    simp only [sub_comp, X_comp, C_comp, neg_comp]; ring
  have hcomp : (p.comp (X - C 2)).comp (-X) = (p.comp (-X)).comp (X + C 2) := by
    rw [comp_assoc, comp_assoc, hlin]
  rw [hcomp]
  have h2 := congrArg sig (Lmom_rec2 (az := az) (p.comp (-X)))
  simp only [map_mul, map_sub, map_pow, sig_zK, sig_ratCast, eval_comp, eval_neg, eval_X] at h2
  have hz := zK_ne_zero (az := az)
  have hzi : (zK az) * (zK az)⁻¹ = 1 := mul_inv_cancel₀ hz
  have key : sig (Lmom az ((p.comp (-X)).comp (X + C 2))) =
      (zK az) ^ 2 * sig (Lmom az (p.comp (-X))) + (zK az) * ((p.eval (-1) : ℚ) : (Qd az)) := by
    linear_combination (zK az) ^ 2 * h2 + ((zK az) * ((p.eval (-1) : ℚ) : (Qd az)) -
      (1 + (zK az) * (zK az)⁻¹) * sig (Lmom az ((p.comp (-X)).comp (X + C 2)))) * hzi
  rw [key]; ring

/-- **Parity of the moments**: `σ(Lmom p) = Lmom(p(−t))`. -/
theorem sig_Lmom (p : ℚ[X]) : sig (Lmom az p) = Lmom az (p.comp (-X)) := by
  have h := congrArg (fun L : ℚ[X] →ₗ[ℚ] (Qd az) => L (p.comp (-X))) LmomRefl_eq
  simp only [LmomRefl, LinearMap.coe_mk, AddHom.coe_mk, comp_assoc, neg_comp, X_comp, neg_neg, comp_X] at h
  exact h

/-- `σ S_n = (−1)^n S_n`. -/
theorem sig_Smom (n : ℕ) : sig (Smom az n) = (-1) ^ n * Smom az n := by
  rw [← Lmom_X_pow, sig_Lmom, X_pow_comp, neg_pow, ← C_1, ← C_neg, ← C_pow, Lmom_C_mul, Algebra.smul_def]
  simp

/-- `μ(R) = Σ_{t odd ≥ 1} z^t R′(t) = Lmom(R′)` on polynomials. -/
noncomputable def muPoly (az : ℕ) [Fact (1 ≤ az)] (R : ℚ[X]) : (Qd az) := Lmom az (derivative R)

lemma muPoly_add (R S : ℚ[X]) : muPoly az (R + S) = muPoly az R + muPoly az S := by
  simp [muPoly, map_add]

lemma muPoly_smul (c : ℚ) (R : ℚ[X]) : muPoly az (c • R) = c • muPoly az R := by
  simp [muPoly, map_smul]

/-- `σ μ(R) = −μ(R(−t))`. -/
theorem sig_muPoly (R : ℚ[X]) : sig (muPoly az R) = -muPoly az (R.comp (-X)) := by
  unfold muPoly
  rw [sig_Lmom, derivative_comp, derivative_neg, derivative_X]
  rw [show (-1 : ℚ[X]) * (derivative R).comp (-X) = (-1 : ℚ) • (derivative R).comp (-X) by
    rw [Algebra.smul_def]; simp]
  rw [map_smul]; simp

end Chi2U
