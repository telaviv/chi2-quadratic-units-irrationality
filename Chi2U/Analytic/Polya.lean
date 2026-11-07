/-
# The lattice energy inequality

`polya_log`: for `M ≥ 1` and real `ν_0, …, ν_{M−1}`,
  `Σ_{i≠j} ν_i ν_j log|i − j| ≤ log 2 · Σ ν_i² + log M · (Σ ν_i)²`.

Proof (Pólya's criterion, finite form): `f(0) = log M + log 2`, `f(d) = log(M/d)` (`1 ≤ d ≤ M`), `f = 0` beyond, is
convex on `ℕ`, so `f(d) = Σ_{k=1}^{M} Δ²f(k)·(k − d)₊` with `Δ²f ≥ 0`; each triangle kernel `(k − |i−j|)₊` is a sum of
squares of window sums. Hence `Σ_{i,j} ν_iν_j f(|i−j|) ≥ 0`, which rearranges to the claim.
This is a discrete form of the weak duality `E(ν) ≤ 0` of potential theory (Saff–Totik, Lemma I.1.8).
(Copied verbatim from `lean_chi2/Chi2Irrational/Analytic/Polya.lean`, namespace renamed `Chi2Irr` → `Chi2U`.)
-/
import Mathlib

namespace Chi2U

open Finset Real

/-- The distance `|i − j|` on `ℕ`. -/
def ndist (i j : ℕ) : ℕ := max i j - min i j

/-- The triangle kernel `(k − |i − j|)₊`. -/
def tri (k i j : ℕ) : ℕ := (k + min i j) - max i j

lemma tri_cast (k i j : ℕ) : (tri k i j : ℝ) = if ndist i j ≤ k then (k : ℝ) - ndist i j else 0 := by
  unfold tri ndist
  split_ifs with h
  · rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_add]; ring
  · rw [show k + min i j - max i j = 0 by omega]; simp

/-- Triangle kernels are positive semidefinite. -/
lemma tri_psd (M k : ℕ) (ν : ℕ → ℝ) :
    0 ≤ ∑ i ∈ range M, ∑ j ∈ range M, ν i * ν j * (tri k i j : ℝ) := by
  set χ : ℕ → ℕ → ℝ := fun m i => if i < m ∧ m ≤ i + k then 1 else 0
  have hwin : ∀ i ∈ range M, ∀ j ∈ range M,
      ∑ m ∈ range (M + k + 1), χ m i * χ m j = (tri k i j : ℝ) := by
    intro i hi j hj
    rw [mem_range] at hi hj
    have : ∀ m, χ m i * χ m j = if (i < m ∧ m ≤ i + k) ∧ (j < m ∧ m ≤ j + k) then (1 : ℝ) else 0 := by
      intro m; simp only [χ]; split_ifs <;> simp_all
    simp_rw [this]
    rw [Finset.sum_boole]
    have hset : (range (M + k + 1)).filter (fun m => (i < m ∧ m ≤ i + k) ∧ (j < m ∧ m ≤ j + k)) =
        Ioc (max i j) (min i j + k) := by
      ext m; simp only [mem_filter, mem_range, mem_Ioc]; omega
    rw [hset, Nat.card_Ioc]
    unfold tri
    congr 1
    omega
  have hsq : 0 ≤ ∑ m ∈ range (M + k + 1), (∑ i ∈ range M, ν i * χ m i) ^ 2 :=
    Finset.sum_nonneg (fun m _ => sq_nonneg _)
  calc (0 : ℝ) ≤ ∑ m ∈ range (M + k + 1), (∑ i ∈ range M, ν i * χ m i) ^ 2 := hsq
    _ = ∑ i ∈ range M, ∑ j ∈ range M, ν i * ν j * (tri k i j : ℝ) := by
      simp_rw [sq, Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [← hwin i hi j hj, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => by ring)

/-- The convex kernel. -/
noncomputable def fP (M d : ℕ) : ℝ :=
  if d = 0 then Real.log M + Real.log 2 else if d ≤ M then Real.log M - Real.log d else 0

/-- Its second differences. -/
noncomputable def aP (M k : ℕ) : ℝ := fP M (k - 1) - 2 * fP M k + fP M (k + 1)

lemma fP_zero (M : ℕ) : fP M 0 = Real.log M + Real.log 2 := by unfold fP; simp

lemma fP_mid {M d : ℕ} (h1 : 1 ≤ d) (h2 : d ≤ M) : fP M d = Real.log M - Real.log d := by
  unfold fP; rw [ite_eq_right (by omega), ite_eq_left h2]

lemma fP_big {M d : ℕ} (h : M < d) : fP M d = 0 := by
  unfold fP; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

lemma fP_self {M : ℕ} (hM : 1 ≤ M) : fP M M = 0 := by
  rw [fP_mid hM le_rfl, sub_self]

lemma log_conc {k : ℕ} (hk : 2 ≤ k) :
    Real.log ((k - 1 : ℕ) : ℝ) + Real.log ((k + 1 : ℕ) : ℝ) ≤ 2 * Real.log k := by
  have hk1 : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k - 1)
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hkp : ((k - 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ≤ (k : ℝ) * k := by
    rw [Nat.cast_sub (by omega)]; push_cast; nlinarith
  have := Real.log_le_log (by positivity) hkp
  rw [Real.log_mul hk1.ne' (by positivity), Real.log_mul hk0.ne' hk0.ne'] at this
  linarith

lemma aP_nonneg {M : ℕ} (hM : 2 ≤ M) {k : ℕ} (hk : 1 ≤ k) : 0 ≤ aP M k := by
  unfold aP
  rcases Nat.lt_or_ge k M with hkM | hkM
  · rcases Nat.eq_or_lt_of_le hk with rfl | hk2
    · rw [show 1 - 1 = 0 by rfl, fP_zero, fP_mid le_rfl (by omega), fP_mid (by norm_num) hM]
      simp; ring_nf; norm_num
    · rw [fP_mid (by omega) (by omega), fP_mid (by omega) (by omega), fP_mid (by omega) (by omega)]
      have := log_conc (show 2 ≤ k by omega)
      linarith
  · rcases Nat.eq_or_lt_of_le hkM with h | hkM'
    · subst h
      rw [fP_mid (by omega) (by omega), fP_self (by omega), fP_big (by omega)]
      have : Real.log ((M - 1 : ℕ) : ℝ) ≤ Real.log M :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < M - 1)) (by exact_mod_cast (by omega : M - 1 ≤ M))
      linarith
    · rw [fP_big (by omega : M < k), fP_big (by omega : M < k + 1)]
      rcases Nat.eq_or_lt_of_le (show M ≤ k - 1 by omega) with h | h
      · rw [← h, fP_self (by omega)]; simp
      · rw [fP_big h]; simp

/-- Summation of second differences against a triangle. -/
lemma sum_second_diff (g : ℕ → ℝ) {d M : ℕ} (hdM : d ≤ M) :
    ∑ k ∈ Icc 1 M, (g (k - 1) - 2 * g k + g (k + 1)) * (if d ≤ k then (k : ℝ) - d else 0) =
      ((M : ℝ) - d) * (g (M + 1) - g M) - (g M - g d) := by
  induction M, hdM using Nat.le_induction with
  | base =>
    rw [Finset.sum_eq_zero]
    · ring
    · intro k hk
      rw [mem_Icc] at hk
      split_ifs with h
      · rw [show (k : ℝ) = d by exact_mod_cast le_antisymm hk.2 h, sub_self, mul_zero]
      · rw [mul_zero]
  | succ M hdM ih =>
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), sum_insert (by simp), ih, ite_eq_left (by omega),
      show M + 1 - 1 = M by omega]
    push_cast
    ring

lemma fP_eq_sum {M : ℕ} (hM : 1 ≤ M) {d : ℕ} (hd : d ≤ M) :
    fP M d = ∑ k ∈ Icc 1 M, aP M k * (if d ≤ k then (k : ℝ) - d else 0) := by
  unfold aP
  rw [sum_second_diff (fP M) hd, fP_self hM, fP_big (by omega : M < M + 1)]
  ring

lemma ndist_cast (i j : ℕ) : ((ndist i j : ℕ) : ℝ) = |(i : ℝ) - j| := by
  unfold ndist
  rcases le_total i j with h | h
  · rw [max_eq_right h, min_eq_left h, Nat.cast_sub h, abs_sub_comm, abs_of_nonneg (by
      have : (i : ℝ) ≤ j := by exact_mod_cast h
      linarith)]
  · rw [max_eq_left h, min_eq_right h, Nat.cast_sub h, abs_of_nonneg (by
      have : (j : ℝ) ≤ i := by exact_mod_cast h
      linarith)]

/-- **The lattice energy inequality.** -/
theorem polya_log {M : ℕ} (hM : 1 ≤ M) (ν : ℕ → ℝ) :
    ∑ i ∈ range M, ∑ j ∈ (range M).erase i, ν i * ν j * Real.log |(i : ℝ) - j| ≤
      Real.log 2 * ∑ i ∈ range M, ν i ^ 2 + Real.log M * (∑ i ∈ range M, ν i) ^ 2 := by
  rcases Nat.eq_or_lt_of_le hM with rfl | hM2
  · simp only [range_one, sum_singleton, Finset.erase_singleton, sum_empty, Nat.cast_one,
      Real.log_one, zero_mul, add_zero]
    exact mul_nonneg (Real.log_nonneg (by norm_num)) (sq_nonneg _)
  have hM2' : 2 ≤ M := hM2
  -- positivity of the convex kernel form
  have hS : 0 ≤ ∑ i ∈ range M, ∑ j ∈ range M, ν i * ν j * fP M (ndist i j) := by
    have hrep : ∀ i ∈ range M, ∀ j ∈ range M, fP M (ndist i j) =
        ∑ k ∈ Icc 1 M, aP M k * (tri k i j : ℝ) := by
      intro i hi j hj
      rw [mem_range] at hi hj
      rw [fP_eq_sum hM (by unfold ndist; omega)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [tri_cast]
    calc (0 : ℝ) ≤ ∑ k ∈ Icc 1 M, aP M k * ∑ i ∈ range M, ∑ j ∈ range M, ν i * ν j * (tri k i j : ℝ) :=
          Finset.sum_nonneg (fun k hk => mul_nonneg (aP_nonneg hM2' (mem_Icc.mp hk).1) (tri_psd M k ν))
      _ = ∑ i ∈ range M, ∑ j ∈ range M, ν i * ν j * fP M (ndist i j) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [hrep i hi j hj, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => by ring)
  -- split off the diagonal
  have hsplit : ∑ i ∈ range M, ∑ j ∈ range M, ν i * ν j * fP M (ndist i j) =
      (Real.log M + Real.log 2) * ∑ i ∈ range M, ν i ^ 2 +
        ∑ i ∈ range M, ∑ j ∈ (range M).erase i, ν i * ν j * (Real.log M - Real.log |(i : ℝ) - j|) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [← Finset.add_sum_erase _ _ hi]
    congr 1
    · unfold ndist; simp [fP_zero]; ring
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      have hji := Finset.ne_of_mem_erase hj
      have hjM := mem_range.mp (Finset.mem_of_mem_erase hj)
      have hiM := mem_range.mp hi
      rw [fP_mid (by unfold ndist; omega) (by unfold ndist; omega), ndist_cast]
  have hoff : ∑ i ∈ range M, ∑ j ∈ (range M).erase i, ν i * ν j =
      (∑ i ∈ range M, ν i) ^ 2 - ∑ i ∈ range M, ν i ^ 2 := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [← Finset.add_sum_erase _ _ hi]
    ring
  have hexp : ∑ i ∈ range M, ∑ j ∈ (range M).erase i, ν i * ν j * (Real.log M - Real.log |(i : ℝ) - j|) =
      Real.log M * ∑ i ∈ range M, ∑ j ∈ (range M).erase i, ν i * ν j -
        ∑ i ∈ range M, ∑ j ∈ (range M).erase i, ν i * ν j * Real.log |(i : ℝ) - j| := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => by ring)
  rw [hsplit, hexp, hoff] at hS
  nlinarith

end Chi2U
