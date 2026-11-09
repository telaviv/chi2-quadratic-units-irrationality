/-
# Theorem V_i: the odd moments `S_e = Σ_{t odd ≥ 1} χ₄(t) z^t t^e` and their parity

**Copy of `Chi2U/Moments.lean`** with the sign fixed (PROOF_TI2 §1: every χ₂ formula with `y = −z²` in place of `z²`).
The trace is `n` (`[Fact (3 ≤ n)]`), so the moment index is called `e` here (it is `n` in the χ₂ file).

`Smom n e ∈ ℚ(√d)` is defined by the recurrence obtained from `t^e − (t−2)^e`, `χ₄(t + 2) = −χ₄(t)` and
`1 + z² = n·z ≠ 0`:

    (1 + z²) S_e = (−1)^e z − Σ_{k<e} C(e,k) (−2)^{e−k} S_k.

`Lmom n : ℚ[X] →ₗ[ℚ] Qt n` is the moment functional `X^e ↦ S_e` (so `Lmom p = Σ_{t odd ≥ 1} χ₄(t) z^t p(t)`; the series
identity is `Ti/MomentSeries.hasSum_Lmom'`). It satisfies
* (rec₁) `Lmom (p(t − 2)) + z² Lmom p = z·p(−1)`,
* (rec₂) `z² Lmom (q(t + 2)) = z·q(1) − Lmom q`,
and **parity**: `σ(Lmom p) = Lmom (p(−t))`, i.e. `σ S_e = (−1)^e S_e` (`sig_Lmom`), the same form as for χ₂.
Proof of parity: `p ↦ σ(Lmom(p(−t)))` also satisfies rec₁ (by rec₂ and `σz = z⁻¹`), and rec₁ has a unique solution.

`muPoly R := Lmom R′` is `μ(R) = Σ_{t odd ≥ 1} χ₄(t) z^t R′(t)`; `σ μ(R) = −μ(R(−t))` (`sig_muPoly`).
-/
import Chi2U.Ti.Field

namespace Chi2U
namespace Ti

variable {n : ℕ} [Fact (3 ≤ n)]

open Polynomial

/-- `S_e = Σ_{t odd ≥ 1} χ₄(t) z^t t^e`, via the recurrence. -/
noncomputable def Smom (n : ℕ) [Fact (3 ≤ n)] : ℕ → (Qt n)
  | e => ((-1) ^ e * (zK n) - ∑ k : Fin e, ((e.choose k : ℕ) : (Qt n)) * (-2) ^ (e - (k : ℕ)) * Smom n k) /
      (1 + (zK n) ^ 2)
termination_by e => e
decreasing_by exact k.isLt

lemma Smom_rec (e : ℕ) :
    (1 + (zK n) ^ 2) * Smom n e =
      (-1) ^ e * (zK n) - ∑ k ∈ Finset.range e, ((e.choose k : ℕ) : (Qt n)) * (-2) ^ (e - k) * Smom n k := by
  rw [Smom, mul_div_cancel₀ _ one_add_zK_sq_ne_zero,
    Finset.sum_range (fun k => ((e.choose k : ℕ) : (Qt n)) * (-2) ^ (e - k) * Smom n k)]

/-- The moment functional `X^e ↦ S_e`. -/
noncomputable def Lmom (n : ℕ) [Fact (3 ≤ n)] : ℚ[X] →ₗ[ℚ] (Qt n) :=
  Polynomial.lsum (fun e => LinearMap.toSpanSingleton ℚ (Qt n) (Smom n e))

lemma Lmom_monomial (e : ℕ) (c : ℚ) : Lmom n (monomial e c) = c • Smom n e := by
  simp [Lmom]

lemma Lmom_X_pow (e : ℕ) : Lmom n (X ^ e) = Smom n e := by
  rw [← monomial_one_right_eq_X_pow, Lmom_monomial, one_smul]

lemma Lmom_C_mul (c : ℚ) (p : ℚ[X]) : Lmom n (C c * p) = c • Lmom n p := by
  rw [← smul_eq_C_mul, map_smul]

lemma Lmom_X_sub_two_pow {L : ℚ[X] →ₗ[ℚ] (Qt n)} (e : ℕ) :
    L ((X - C 2) ^ e) = ∑ k ∈ Finset.range (e + 1), ((e.choose k : ℕ) : (Qt n)) * (-2) ^ (e - k) * L (X ^ k) := by
  rw [X_sub_two_pow, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← smul_eq_C_mul, map_smul]
  rw [Algebra.smul_def]
  simp

/-- (rec₁) `Lmom(p(t−2)) + z² Lmom(p) = z p(−1)`. -/
lemma Lmom_rec1 (p : ℚ[X]) :
    Lmom n (p.comp (X - C 2)) + (zK n) ^ 2 * Lmom n p = (zK n) * ((p.eval (-1) : ℚ) : (Qt n)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [add_comp, map_add, map_add, eval_add]; push_cast; linear_combination hp + hq
  | monomial e c =>
      rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, Lmom_C_mul, Lmom_C_mul,
        Lmom_X_sub_two_pow, Lmom_X_pow, Finset.sum_range_succ]
      simp only [Lmom_X_pow, Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, one_mul, eval_mul, eval_C,
        eval_pow, eval_X]
      have hrec := Smom_rec (n := n) e
      simp only [Algebra.smul_def, eq_ratCast]
      push_cast
      linear_combination (c : (Qt n)) * hrec

/-- (rec₂) `z² Lmom(q(t+2)) = z q(1) − Lmom q`. -/
lemma Lmom_rec2 (q : ℚ[X]) :
    (zK n) ^ 2 * Lmom n (q.comp (X + C 2)) = (zK n) * ((q.eval 1 : ℚ) : (Qt n)) - Lmom n q := by
  have h := Lmom_rec1 (n := n) (q.comp (X + C 2))
  rw [comp_assoc, show (X + C 2 : ℚ[X]).comp (X - C 2) = X by simp, comp_X, eval_comp] at h
  simp only [eval_add, eval_X, eval_C] at h
  norm_num at h
  linear_combination h

/-- rec₁ determines the functional: two solutions agree. -/
lemma eq_Lmom_of_rec1 (L : ℚ[X] →ₗ[ℚ] (Qt n))
    (hL : ∀ p : ℚ[X], L (p.comp (X - C 2)) + (zK n) ^ 2 * L p = (zK n) * ((p.eval (-1) : ℚ) : (Qt n))) :
    L = Lmom n := by
  set Δ := L - Lmom n with hΔ
  have hhom : ∀ p : ℚ[X], Δ (p.comp (X - C 2)) = -(zK n) ^ 2 * Δ p := by
    intro p
    have h1 := hL p
    have h2 := Lmom_rec1 (n := n) p
    simp only [hΔ, LinearMap.sub_apply]
    linear_combination h1 - h2
  have hX : ∀ e, Δ (X ^ e) = 0 := by
    intro e
    induction e using Nat.strong_induction_on with
    | _ e ih =>
      have h := hhom (X ^ e)
      rw [X_pow_comp, Lmom_X_sub_two_pow, Finset.sum_range_succ,
        Finset.sum_eq_zero (fun k hk => by rw [ih k (Finset.mem_range.mp hk), mul_zero])] at h
      simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, one_mul, zero_add] at h
      have h' : (1 + (zK n) ^ 2) * Δ (X ^ e) = 0 := by linear_combination h
      exact (mul_eq_zero.mp h').resolve_left one_add_zK_sq_ne_zero
  have : Δ = 0 := by
    refine Polynomial.lhom_ext' (fun e => LinearMap.ext_ring ?_)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, monomial_one_right_eq_X_pow]
    exact hX e
  rw [hΔ, sub_eq_zero] at this
  exact this

/-- `p ↦ σ(Lmom(p(−t)))` as a `ℚ`-linear map. -/
noncomputable def LmomRefl (n : ℕ) [Fact (3 ≤ n)] : ℚ[X] →ₗ[ℚ] (Qt n) where
  toFun p := sig (Lmom n (p.comp (-X)))
  map_add' p q := by rw [add_comp, map_add, map_add]
  map_smul' c p := by
    rw [smul_comp, map_smul, sig_smul]; rfl

lemma LmomRefl_eq : LmomRefl n = Lmom n := by
  apply eq_Lmom_of_rec1
  intro p
  show sig (Lmom n ((p.comp (X - C 2)).comp (-X))) + (zK n) ^ 2 * sig (Lmom n (p.comp (-X))) =
    (zK n) * ((p.eval (-1) : ℚ) : (Qt n))
  have hlin : (X - C 2 : ℚ[X]).comp (-X) = (-X).comp (X + C 2) := by
    simp only [sub_comp, X_comp, C_comp, neg_comp]; ring
  have hcomp : (p.comp (X - C 2)).comp (-X) = (p.comp (-X)).comp (X + C 2) := by
    rw [comp_assoc, comp_assoc, hlin]
  rw [hcomp]
  have h2 := congrArg sig (Lmom_rec2 (n := n) (p.comp (-X)))
  simp only [map_mul, map_sub, map_pow, sig_zK, sig_ratCast, eval_comp, eval_neg, eval_X] at h2
  have hz := zK_ne_zero (n := n)
  have hzi : (zK n) * (zK n)⁻¹ = 1 := mul_inv_cancel₀ hz
  -- `h2 : z⁻² σL(q(t+2)) = z⁻¹ p(−1) − σL(q)`, `q = p(−t)`
  have key : sig (Lmom n ((p.comp (-X)).comp (X + C 2))) =
      (zK n) * ((p.eval (-1) : ℚ) : (Qt n)) - (zK n) ^ 2 * sig (Lmom n (p.comp (-X))) := by
    linear_combination (zK n) ^ 2 * h2 + ((zK n) * ((p.eval (-1) : ℚ) : (Qt n)) -
      (1 + (zK n) * (zK n)⁻¹) * sig (Lmom n ((p.comp (-X)).comp (X + C 2)))) * hzi
  rw [key]; ring

/-- **Parity of the moments**: `σ(Lmom p) = Lmom(p(−t))`. -/
theorem sig_Lmom (p : ℚ[X]) : sig (Lmom n p) = Lmom n (p.comp (-X)) := by
  have h := congrArg (fun L : ℚ[X] →ₗ[ℚ] (Qt n) => L (p.comp (-X))) LmomRefl_eq
  simp only [LmomRefl, LinearMap.coe_mk, AddHom.coe_mk, comp_assoc, neg_comp, X_comp, neg_neg, comp_X] at h
  exact h

/-- `σ S_e = (−1)^e S_e`. -/
theorem sig_Smom (e : ℕ) : sig (Smom n e) = (-1) ^ e * Smom n e := by
  rw [← Lmom_X_pow, sig_Lmom, X_pow_comp, neg_pow, ← C_1, ← C_neg, ← C_pow, Lmom_C_mul, Algebra.smul_def]
  simp

/-- `μ(R) = Σ_{t odd ≥ 1} χ₄(t) z^t R′(t) = Lmom(R′)` on polynomials. -/
noncomputable def muPoly (n : ℕ) [Fact (3 ≤ n)] (R : ℚ[X]) : (Qt n) := Lmom n (derivative R)

lemma muPoly_add (R S : ℚ[X]) : muPoly n (R + S) = muPoly n R + muPoly n S := by
  simp [muPoly, map_add]

lemma muPoly_smul (c : ℚ) (R : ℚ[X]) : muPoly n (c • R) = c • muPoly n R := by
  simp [muPoly, map_smul]

/-- `σ μ(R) = −μ(R(−t))`. -/
theorem sig_muPoly (R : ℚ[X]) : sig (muPoly n R) = -muPoly n (R.comp (-X)) := by
  unfold muPoly
  rw [sig_Lmom, derivative_comp, derivative_neg, derivative_X]
  rw [show (-1 : ℚ[X]) * (derivative R).comp (-X) = (-1 : ℚ) • (derivative R).comp (-X) by
    rw [Algebra.smul_def]; simp]
  rw [map_smul]; simp

end Ti
end Chi2U
