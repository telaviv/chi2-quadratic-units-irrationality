/-
# Theorem V_i: the moment series over `ℝ`

**Copy of `Chi2U/MomentSeries.lean`** with the sign fixed (weights `χ₄(2s+1) = (−1)^s`).

`R_e = Σ_{s ≥ 0} (−1)^s z^{2s+1} (2s+1)^e` (`z = zT n ∈ (0, 1)`) converges absolutely and equals `emb S_e`
(`hasSum_Smom'`): the real series satisfies the recurrence defining `Smom` (shift `s ↦ s + 1`, which multiplies the
terms by `−z²`, and `(2s−1)^e = ((2s+1) − 2)^e`). By linearity `Σ_s (−1)^s z^{2s+1} p(2s+1) = emb (Lmom p)`
(`hasSum_Lmom'`).
-/
import Chi2U.Ti.Moments

namespace Chi2U
namespace Ti

variable {n : ℕ} [Fact (3 ≤ n)]

open Polynomial Finset Filter

/-- `z² − n·z + 1 = 0` over `ℝ`. -/
lemma zT_sq_sub : (zT n) ^ 2 - (n : ℝ) * (zT n) + 1 = 0 := by
  have h5 := sqrt_mul_self_dT (n := n)
  unfold zT; linear_combination h5

/-- `1 + z² = n·z` over `ℝ`. -/
lemma one_add_zT_sq : 1 + (zT n) ^ 2 = (n : ℝ) * (zT n) := by linear_combination (zT_sq_sub (n := n))

lemma one_add_zT_sq_ne_zero : (1 : ℝ) + (zT n) ^ 2 ≠ 0 := by positivity

lemma emb_injective : Function.Injective (emb (n := n)) := emb.injective

/-- The absolute terms `z^{2s+1} (2s+1)^e`. -/
noncomputable def rAbs (n : ℕ) (e s : ℕ) : ℝ := (zT n) ^ (2 * s + 1) * ((2 * s + 1 : ℕ) : ℝ) ^ e

/-- The terms `(−1)^s z^{2s+1} (2s+1)^e`. -/
noncomputable def rTerm (n : ℕ) (e s : ℕ) : ℝ := (-1) ^ s * (zT n) ^ (2 * s + 1) * ((2 * s + 1 : ℕ) : ℝ) ^ e

lemma summable_rAbs (e : ℕ) : Summable (rAbs n e) := by
  have hy : ‖(zT n) ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by have := zT_pos (n := n); positivity)]
    have := zT_pos (n := n); have := zT_lt_one (n := n); nlinarith
  have h1 : Summable (fun s : ℕ => ((s : ℝ) ^ e) * ((zT n) ^ 2) ^ s) := summable_pow_mul_geometric_of_norm_lt_one e hy
  have h2 : Summable (fun s : ℕ => ((zT n) ^ 2) ^ s) := summable_geometric_of_norm_lt_one hy
  have hs : Summable (fun s : ℕ => (zT n) * 3 ^ e * (((s : ℝ) ^ e) * ((zT n) ^ 2) ^ s + ((zT n) ^ 2) ^ s)) :=
    (h1.add h2).mul_left _
  refine Summable.of_nonneg_of_le (fun s => ?_) (fun s => ?_) hs
  · unfold rAbs; have := zT_pos (n := n); positivity
  · unfold rAbs
    have hz := zT_pos (n := n)
    have hb : ((2 * s + 1 : ℕ) : ℝ) ^ e ≤ 3 ^ e * ((s : ℝ) ^ e + 1) := by
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · simp only [CharP.cast_eq_zero, mul_zero, zero_add, Nat.cast_one, one_pow]
        have : (1 : ℝ) ≤ 3 ^ e := one_le_pow₀ (by norm_num)
        have : (0 : ℝ) ≤ 0 ^ e := by positivity
        nlinarith
      · have h3 : ((2 * s + 1 : ℕ) : ℝ) ≤ 3 * s := by
          push_cast; have : (1 : ℝ) ≤ s := by exact_mod_cast hs
          linarith
        calc ((2 * s + 1 : ℕ) : ℝ) ^ e ≤ (3 * (s : ℝ)) ^ e := pow_le_pow_left₀ (by positivity) h3 e
          _ = 3 ^ e * (s : ℝ) ^ e := mul_pow _ _ _
          _ ≤ 3 ^ e * ((s : ℝ) ^ e + 1) := by gcongr; linarith
    calc (zT n) ^ (2 * s + 1) * ((2 * s + 1 : ℕ) : ℝ) ^ e
        ≤ (zT n) ^ (2 * s + 1) * (3 ^ e * ((s : ℝ) ^ e + 1)) := by gcongr
      _ = (zT n) * 3 ^ e * (((s : ℝ) ^ e) * ((zT n) ^ 2) ^ s + ((zT n) ^ 2) ^ s) := by
          rw [pow_succ, pow_mul]; ring

lemma summable_rTerm (e : ℕ) : Summable (rTerm n e) := by
  refine Summable.of_norm_bounded (summable_rAbs (n := n) e) (fun s => ?_)
  unfold rTerm rAbs
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (pow_pos zT_pos _), abs_of_nonneg (by positivity)]

/-- `Σ_k C(e,k)(−2)^{e−k} R_k = −z² R_e + z(−1)^e`, from the shift. -/
lemma rec_real (e : ℕ) :
    ∑ k ∈ range (e + 1), ((e.choose k : ℕ) : ℝ) * (-2) ^ (e - k) * ∑' s, rTerm n k s =
      -(zT n) ^ 2 * ∑' s, rTerm n e s + (zT n) * (-1) ^ e := by
  set g : ℕ → ℝ := fun s => (-1) ^ s * (zT n) ^ (2 * s + 1) * (2 * (s : ℝ) - 1) ^ e with hg
  have hshift : HasSum (fun s => g (s + 1)) (-(zT n) ^ 2 * ∑' s, rTerm n e s) := by
    have := ((summable_rTerm (n := n) e).hasSum).mul_left (-(zT n) ^ 2)
    convert this using 1
    funext s; simp only [hg, rTerm]; push_cast; ring
  have hg1 : HasSum g (-(zT n) ^ 2 * ∑' s, rTerm n e s + (zT n) * (-1) ^ e) := by
    convert (hasSum_nat_add_iff (f := g) 1).mp hshift using 1
    simp [hg]
  have hg2 : HasSum g (∑ k ∈ range (e + 1), ((e.choose k : ℕ) : ℝ) * (-2) ^ (e - k) * ∑' s, rTerm n k s) := by
    have := hasSum_sum (s := range (e + 1)) (fun k _ =>
      ((summable_rTerm (n := n) k).hasSum).mul_left (((e.choose k : ℕ) : ℝ) * (-2) ^ (e - k)))
    convert this using 1
    funext s
    simp only [hg, rTerm]
    rw [show (2 * (s : ℝ) - 1) = ((2 * s + 1 : ℕ) : ℝ) + (-2) by push_cast; ring, add_pow, mul_sum]
    refine sum_congr rfl (fun k _ => ?_)
    ring
  exact hg2.unique hg1

/-- `Σ_s (−1)^s z^{2s+1}(2s+1)^e = emb S_e`. -/
theorem hasSum_Smom' (e : ℕ) : HasSum (rTerm n e) (emb (Smom n e)) := by
  suffices h : ∀ e, ∑' s, rTerm n e s = emb (Smom n e) by
    rw [← h e]; exact (summable_rTerm e).hasSum
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    have hr := rec_real (n := n) e
    rw [sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero] at hr
    rw [sum_congr rfl (fun k hk => by rw [ih k (mem_range.mp hk)])] at hr
    have hS := congrArg emb (Smom_rec (n := n) e)
    simp only [map_mul, map_sub, map_add, map_one, map_pow, map_sum, map_neg, map_natCast, emb_zK,
      map_ofNat] at hS
    have hne := one_add_zT_sq_ne_zero (n := n)
    have key : (1 + (zT n) ^ 2) * ∑' s, rTerm n e s = (1 + (zT n) ^ 2) * emb (Smom n e) := by
      rw [hS]
      push_cast at hr ⊢
      linear_combination hr
    exact mul_left_cancel₀ hne key

/-- `Σ_s (−1)^s z^{2s+1} p(2s+1) = emb (Lmom p)`. -/
theorem hasSum_Lmom' (p : ℚ[X]) :
    HasSum (fun s : ℕ => (-1) ^ s * (zT n) ^ (2 * s + 1) * aeval ((2 * s + 1 : ℕ) : ℝ) p) (emb (Lmom n p)) := by
  have hL : Lmom n p = ∑ e ∈ range (p.natDegree + 1), p.coeff e • Smom n e := by
    conv_lhs => rw [p.as_sum_range' (p.natDegree + 1) (Nat.lt_succ_self _)]
    rw [map_sum]
    refine sum_congr rfl (fun e _ => ?_)
    rw [Lmom_monomial]
  have := hasSum_sum (s := range (p.natDegree + 1)) (fun e _ =>
    (hasSum_Smom' (n := n) e).mul_left ((p.coeff e : ℚ) : ℝ))
  rw [hL, map_sum]
  convert this using 1
  · funext s
    rw [aeval_eq_sum_range, mul_sum]
    refine sum_congr rfl (fun e _ => ?_)
    simp only [rTerm, Algebra.smul_def, eq_ratCast]
    rw [← eq_ratCast (algebraMap ℚ ℝ)]; simp; ring
  · refine sum_congr rfl (fun e _ => ?_)
    rw [Algebra.smul_def, map_mul, eq_ratCast, map_ratCast]

end Ti
end Chi2U
