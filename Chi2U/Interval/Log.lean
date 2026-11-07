/-
# Verified enclosures of `log` at rational points

Argument reduction `q = 2^k m` with `m ∈ [2/3, 4/3]`, then the series of `log (1 - x)` with Mathlib's explicit tail
bound `Real.abs_log_sub_add_sum_range_le`; `log 2` by the same series at `x = 1/2` (dyadic enclosure of width
`2^{-100}`, checked against the series by the kernel).
Ported from the `log` part of `BetaIrrational/Interval/Elem.lean` in https://github.com/telaviv/beta-irrationality.
Copied verbatim from `lean_chi2/Chi2Irrational/Interval/Log.lean` (namespace `Chi2Irr` → `Chi2U`).
-/
import Chi2U.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Chi2U.Interval

open IV Finset

/-! ## `log` -/

/-- `Σ_{i<n} x^(i+1)/(i+1)`. -/
def lser (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => lser x n + x ^ (n + 1) / (n + 1)

lemma lser_cast (x : ℚ) (n : ℕ) :
    ((lser x n : ℚ) : ℝ) = ∑ i ∈ range n, (x : ℝ) ^ (i + 1) / (i + 1) := by
  induction n with
  | zero => simp [lser]
  | succ n ih => rw [lser, sum_range_succ, ← ih]; push_cast; ring

/-- Enclosure of `log (1 - x)` (for `|x| < 1`). -/
def logOneSub (x : ℚ) (n : ℕ) : IV :=
  if |x| < 1 then
    ival (-lser x n - |x| ^ (n + 1) / (1 - |x|)) (-lser x n + |x| ^ (n + 1) / (1 - |x|))
  else top

lemma mem_logOneSub (x : ℚ) (n : ℕ) : (logOneSub x n).mem (Real.log (1 - x)) := by
  unfold logOneSub
  split_ifs with hx
  · have hx' : |(x : ℝ)| < 1 := by exact_mod_cast hx
    have h := Real.abs_log_sub_add_sum_range_le hx' n
    rw [← lser_cast, abs_le] at h
    simp only [mem, Rat.cast_sub, Rat.cast_add, Rat.cast_neg, Rat.cast_div, Rat.cast_pow,
      Rat.cast_abs, Rat.cast_one]
    constructor <;> linarith [h.1, h.2]
  · trivial

/-- Series enclosure of `log 2`. -/
def log2S : IV := (logOneSub (1 / 2) 110).neg

lemma mem_log2S : log2S.mem (Real.log 2) := by
  have h := mem_neg (mem_logOneSub (1 / 2) 110)
  have : Real.log 2 = -Real.log (1 - ((1 / 2 : ℚ) : ℝ)) := by
    rw [show (1 : ℝ) - ((1 / 2 : ℚ) : ℝ) = (2 : ℝ)⁻¹ by push_cast; norm_num, Real.log_inv, neg_neg]
  rw [this]; exact h

/-- Dyadic enclosure of `log 2` (width `2^{-100}`), checked against the series. -/
def log2I : IV :=
  ival (878668439483319573618263538048 / 2 ^ 100) (878668439483319573618263538049 / 2 ^ 100)

lemma log2S_lo : log2S.loGe (878668439483319573618263538048 / 2 ^ 100) = true := by decide +kernel
lemma log2S_hi : log2S.hiLe (878668439483319573618263538049 / 2 ^ 100) = true := by decide +kernel

lemma mem_log2I : log2I.mem (Real.log 2) :=
  ⟨ge_of_loGe mem_log2S log2S_lo, le_of_hiLe mem_log2S log2S_hi⟩

/-- Exponent `k` with `q / 2^k ∈ [2/3, 4/3]` (for `q > 0`; any `k` is sound). -/
def kOf (q : ℚ) : ℤ :=
  let k0 : ℤ := (q.num.natAbs.log2 : ℤ) - (q.den.log2 : ℤ)
  if 4 / 3 < q / 2 ^ k0 then k0 + 1 else if q / 2 ^ k0 < 2 / 3 then k0 - 1 else k0

/-- Enclosure of `log q` at a rational point. -/
def logPt (n : ℕ) (q : ℚ) : IV :=
  if 0 < q then (log2I.smul (kOf q : ℚ)).add (logOneSub (1 - q / 2 ^ kOf q) n) else top

lemma mem_logPt (n : ℕ) (q : ℚ) : (logPt n q).mem (Real.log q) := by
  unfold logPt
  split_ifs with hq
  · set k := kOf q
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have h2 : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
    have hsplit : Real.log q = (k : ℝ) * Real.log 2 + Real.log (1 - ((1 - q / 2 ^ k : ℚ) : ℝ)) := by
      have : (1 : ℝ) - ((1 - q / 2 ^ k : ℚ) : ℝ) = (q : ℝ) / 2 ^ k := by push_cast; ring
      rw [this, Real.log_div hq'.ne' h2.ne', Real.log_zpow]; ring
    rw [hsplit]
    have := mem_smul (k : ℚ) mem_log2I
    push_cast at this
    exact mem_add this (mem_logOneSub _ n)
  · trivial

end Chi2U.Interval
