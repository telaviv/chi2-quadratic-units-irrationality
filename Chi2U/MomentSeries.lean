/-
# The moment series over `ℝ`

`R_n = Σ_{s ≥ 0} z^{2s+1} (2s+1)^n` (`z = √5 − 2 ∈ (0, 1)`) converges and equals `emb S_n` (`hasSum_Smom'`):
the real series satisfies the recurrence defining `Smom` (shift `s ↦ s + 1` and `(2s−1)^n = ((2s+1) − 2)^n`).
By linearity `Σ_s z^{2s+1} p(2s+1) = emb (Lmom p)` (`hasSum_Lmom'`).
-/
import Chi2U.Moments

namespace Chi2U

open Polynomial Finset Filter

lemma zU_sq_add : zU ^ 2 + 4 * zU = 1 := by
  have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  unfold zU; nlinarith

lemma one_sub_zU_sq_ne_zero : (1 : ℝ) - zU ^ 2 ≠ 0 := by
  have := zU_pos; have := zU_lt_one; nlinarith

lemma emb_injective : Function.Injective emb := emb.injective

/-- The terms `z^{2s+1} (2s+1)^n`. -/
noncomputable def rTerm (n s : ℕ) : ℝ := zU ^ (2 * s + 1) * ((2 * s + 1 : ℕ) : ℝ) ^ n

lemma summable_rTerm (n : ℕ) : Summable (rTerm n) := by
  have hy : ‖zU ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by have := zU_pos; positivity)]
    have := zU_pos; have := zU_lt_one; nlinarith
  have h1 : Summable (fun s : ℕ => ((s : ℝ) ^ n) * (zU ^ 2) ^ s) := summable_pow_mul_geometric_of_norm_lt_one n hy
  have h2 : Summable (fun s : ℕ => (zU ^ 2) ^ s) := summable_geometric_of_norm_lt_one hy
  have hs : Summable (fun s : ℕ => zU * 3 ^ n * (((s : ℝ) ^ n) * (zU ^ 2) ^ s + (zU ^ 2) ^ s)) :=
    (h1.add h2).mul_left _
  refine Summable.of_nonneg_of_le (fun s => ?_) (fun s => ?_) hs
  · unfold rTerm; have := zU_pos; positivity
  · unfold rTerm
    have hz := zU_pos
    have hb : ((2 * s + 1 : ℕ) : ℝ) ^ n ≤ 3 ^ n * ((s : ℝ) ^ n + 1) := by
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · simp only [CharP.cast_eq_zero, mul_zero, zero_add, Nat.cast_one, one_pow]
        have : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
        have : (0 : ℝ) ≤ 0 ^ n := by positivity
        nlinarith
      · have h3 : ((2 * s + 1 : ℕ) : ℝ) ≤ 3 * s := by
          push_cast; have : (1 : ℝ) ≤ s := by exact_mod_cast hs
          linarith
        calc ((2 * s + 1 : ℕ) : ℝ) ^ n ≤ (3 * (s : ℝ)) ^ n := pow_le_pow_left₀ (by positivity) h3 n
          _ = 3 ^ n * (s : ℝ) ^ n := mul_pow _ _ _
          _ ≤ 3 ^ n * ((s : ℝ) ^ n + 1) := by gcongr; linarith
    calc zU ^ (2 * s + 1) * ((2 * s + 1 : ℕ) : ℝ) ^ n
        ≤ zU ^ (2 * s + 1) * (3 ^ n * ((s : ℝ) ^ n + 1)) := by gcongr
      _ = zU * 3 ^ n * (((s : ℝ) ^ n) * (zU ^ 2) ^ s + (zU ^ 2) ^ s) := by rw [pow_succ, pow_mul]; ring

/-- `Σ_k C(n,k)(−2)^{n−k} R_k = z² R_n + z(−1)^n`, from the shift. -/
lemma rec_real (n : ℕ) :
    ∑ k ∈ range (n + 1), ((n.choose k : ℕ) : ℝ) * (-2) ^ (n - k) * ∑' s, rTerm k s =
      zU ^ 2 * ∑' s, rTerm n s + zU * (-1) ^ n := by
  set g : ℕ → ℝ := fun s => zU ^ (2 * s + 1) * (2 * (s : ℝ) - 1) ^ n with hg
  have hshift : HasSum (fun s => g (s + 1)) (zU ^ 2 * ∑' s, rTerm n s) := by
    have := ((summable_rTerm n).hasSum).mul_left (zU ^ 2)
    convert this using 1
    funext s; simp only [hg, rTerm]; push_cast; ring
  have hg1 : HasSum g (zU ^ 2 * ∑' s, rTerm n s + zU * (-1) ^ n) := by
    convert (hasSum_nat_add_iff (f := g) 1).mp hshift using 1
    simp [hg]
  have hg2 : HasSum g (∑ k ∈ range (n + 1), ((n.choose k : ℕ) : ℝ) * (-2) ^ (n - k) * ∑' s, rTerm k s) := by
    have := hasSum_sum (s := range (n + 1)) (fun k _ =>
      ((summable_rTerm k).hasSum).mul_left (((n.choose k : ℕ) : ℝ) * (-2) ^ (n - k)))
    convert this using 1
    funext s
    simp only [hg, rTerm]
    rw [show (2 * (s : ℝ) - 1) = ((2 * s + 1 : ℕ) : ℝ) + (-2) by push_cast; ring, add_pow, mul_sum]
    refine sum_congr rfl (fun k _ => ?_)
    ring
  exact hg2.unique hg1

/-- `Σ_s z^{2s+1}(2s+1)^n = emb S_n`. -/
theorem hasSum_Smom' (n : ℕ) : HasSum (rTerm n) (emb (Smom n)) := by
  suffices h : ∀ n, ∑' s, rTerm n s = emb (Smom n) by
    rw [← h n]; exact (summable_rTerm n).hasSum
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hr := rec_real n
    rw [sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero] at hr
    rw [sum_congr rfl (fun k hk => by rw [ih k (mem_range.mp hk)])] at hr
    have hS := congrArg emb (Smom_rec n)
    simp only [map_mul, map_sub, map_one, map_pow, map_sum, map_neg, map_natCast, emb_zK, map_ofNat] at hS
    have hne := one_sub_zU_sq_ne_zero
    have key : (1 - zU ^ 2) * ∑' s, rTerm n s = (1 - zU ^ 2) * emb (Smom n) := by
      rw [hS]
      push_cast at hr ⊢
      linear_combination hr
    exact mul_left_cancel₀ hne key

/-- `Σ_s z^{2s+1} p(2s+1) = emb (Lmom p)`. -/
theorem hasSum_Lmom' (p : ℚ[X]) :
    HasSum (fun s : ℕ => zU ^ (2 * s + 1) * aeval ((2 * s + 1 : ℕ) : ℝ) p) (emb (Lmom p)) := by
  have hL : Lmom p = ∑ n ∈ range (p.natDegree + 1), p.coeff n • Smom n := by
    conv_lhs => rw [p.as_sum_range' (p.natDegree + 1) (Nat.lt_succ_self _)]
    rw [map_sum]
    refine sum_congr rfl (fun n _ => ?_)
    rw [Lmom_monomial]
  have := hasSum_sum (s := range (p.natDegree + 1)) (fun n _ => (hasSum_Smom' n).mul_left ((p.coeff n : ℚ) : ℝ))
  rw [hL, map_sum]
  convert this using 1
  · funext s
    rw [aeval_eq_sum_range, mul_sum]
    refine sum_congr rfl (fun n _ => ?_)
    simp only [rTerm, Algebra.smul_def, eq_ratCast]
    rw [← eq_ratCast (algebraMap ℚ ℝ)]; simp; ring
  · refine sum_congr rfl (fun n _ => ?_)
    rw [Algebra.smul_def, map_mul, eq_ratCast, map_ratCast]

end Chi2U
