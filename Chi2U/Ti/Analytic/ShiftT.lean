/-
# Theorem V_i: the shift lemma (PROOF_TI2 §2 row "§5.2 shift lemma", PROOF_V §5.2) into `DualCertT`

**Copy of `Chi2U/V/Shift.lean`** (`shift_lemma_proof`), target `DualCertT n` instead of `DualCertU az`:
from a dual certificate `C` at Theorem U's unit (`z₂ = zU 4 = √5 − 2`) and `δ > 0`, a certificate `C'` at `z = zT n`
with `Φ(C') ≤ Φ(C) − L/2 + δ`, `L = LshiftT n = log z₂ − log z_n ≥ 0` (`n ≥ 5`, `zT_le_zU_four`).
The construction and proof are Shift.lean's verbatim (`v_n(x) = v₂(x) − L·x`, `vT_shift`; grid refined by `r`,
`L/(2r) ≤ δ`); the elementary sums `V.sum_hinge`, `V.sum_range_mul_div` are reused. Same departure from PROOF_V as
Shift.lean: the left-endpoint Riemann sum costs `L/(2N)`, absorbed by `δ`.
-/
import Chi2U.Ti.Analytic.TheoremBT
import Chi2U.V.Shift

namespace Chi2U
namespace Ti

open Finset

variable {n : ℕ} [Fact (3 ≤ n)]

/-- `v_n(x) = v₂(x) − L·x` (machine at `zT n` versus Theorem U's `zU 4`). -/
lemma vT_shift (n : ℕ) (x : ℝ) : vT n x = vU 4 x - LshiftT n * x := by
  unfold vT vU LshiftT; ring

lemma LshiftT_nonneg (hn5 : 5 ≤ n) : 0 ≤ LshiftT n := by
  unfold LshiftT
  have := Real.log_le_log zT_pos (zT_le_zU_four hn5)
  linarith

/-- **Shift lemma** (PROOF_TI2 §2, PROOF_V §5.2) from Theorem U's certificate into `DualCertT n`. -/
theorem shift_lemma_proof (C : DualCertU 4) (hn5 : 5 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C' : DualCertT n, C'.Phi ≤ C.Phi - LshiftT n / 2 + δ := by
  set Lsh := LshiftT n with hLsh
  have hL0 : 0 ≤ Lsh := LshiftT_nonneg hn5
  -- the refinement factor
  set r : ℕ := ⌈Lsh / δ⌉₊ + 1 with hr
  have hr0 : 0 < r := Nat.succ_pos _
  have hrδ : Lsh / δ ≤ r := by
    have := Nat.le_ceil (Lsh / δ)
    rw [hr]; push_cast; linarith
  have hL1 := C.hL
  set N : ℕ := r * C.L with hN
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hr0.ne' (by omega))
  have hNr : (N : ℝ) = r * C.L := by rw [hN]; push_cast; ring
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hLpos : (0 : ℝ) < C.L := by exact_mod_cast (show 0 < C.L by omega)
  have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hlogz : Real.log (zT n) ≤ Real.log (zU 4) := by unfold LshiftT at hLsh; linarith
  have hX4 : (4 : ℝ) ≤ C.X := by exact_mod_cast C.hX
  refine ⟨{
    μ := C.μ
    hc1 := C.hc1
    hsupp := C.hsupp
    lam := C.lam - Lsh
    L := N
    X := C.X
    Sk := fun k => C.Sk (k / r) - Lsh * (k : ℝ) / N
    hL := hN1
    hX := C.hX
    hF := ?_
    htail1 := by have := C.htail1; linarith
    htail2 := ?_ }, ?_⟩
  · -- the cell bounds
    intro k hk x hx1 hx2
    have hk' : k / r < C.X * C.L := by
      rw [Nat.div_lt_iff_lt_mul hr0]
      calc k < C.X * N := hk
        _ = C.X * C.L * r := by rw [hN]; ring
    have hlo : ((k / r : ℕ) : ℝ) / C.L ≤ x := by
      have h1 : ((k / r : ℕ) : ℝ) * r ≤ k := by exact_mod_cast Nat.div_mul_le_self k r
      refine le_trans ?_ hx1
      rw [hNr, div_le_div_iff₀ hLpos (by positivity)]
      nlinarith
    have hhi : x ≤ (((k / r : ℕ) : ℝ) + 1) / C.L := by
      have h1 : k + 1 ≤ k / r * r + r := Nat.lt_div_mul_add hr0
      have h1' : (k : ℝ) + 1 ≤ ((k / r : ℕ) : ℝ) * r + r := by exact_mod_cast h1
      refine le_trans hx2 ?_
      rw [hNr, div_le_div_iff₀ (by positivity) hLpos]
      nlinarith
    have hF := C.hF (k / r) hk' x hlo hhi
    have hxk : (k : ℝ) / N ≤ x := hx1
    have hmul : Lsh * ((k : ℝ) / N) ≤ Lsh * x := mul_le_mul_of_nonneg_left hxk hL0
    rw [vT_shift n x, ← hLsh]
    change 2 * C.μ.U x + (vU 4 x - Lsh * x) ≤ C.Sk (k / r) - Lsh * (k : ℝ) / N
    rw [mul_div_assoc]
    linarith
  · -- the second tail: it changes by `−(X − 1)·L ≤ 0`
    have h2 := C.htail2
    have hXL : 0 ≤ ((C.X : ℝ) - 1) * Lsh := mul_nonneg (by linarith) hL0
    have e : (C.X : ℝ) * Real.log (zT n) = C.X * Real.log (zU 4) - C.X * Lsh := by
      rw [hLsh]; unfold LshiftT; ring
    change 2 * Real.log C.X - Real.log ((C.X : ℝ) - 1) + C.X * Real.log (zT n) - (C.lam - Lsh) < 0
    rw [e]
    nlinarith
  · -- the exponent
    unfold DualCertT.Phi DualCertU.Phi DualCertT.σ DualCertU.σ
    dsimp only
    have hterm : ∀ k ∈ range (C.X * N), max (C.Sk (k / r) - Lsh * (k : ℝ) / N - (C.lam - Lsh)) 0 ≤
        max (C.Sk (k / r) - C.lam) 0 + Lsh * max (1 - (k : ℝ) / N) 0 := by
      intro k _
      have a1 := le_max_left (C.Sk (k / r) - C.lam) 0
      have a2 := le_max_right (C.Sk (k / r) - C.lam) 0
      have b1 := mul_le_mul_of_nonneg_left (le_max_left (1 - (k : ℝ) / N) 0) hL0
      have b2 := mul_nonneg hL0 (le_max_right (1 - (k : ℝ) / N) 0)
      apply max_le
      · have : Lsh * (1 - (k : ℝ) / N) = Lsh - Lsh * (k : ℝ) / N := by ring
        linarith
      · linarith
    have hsum := sum_le_sum hterm
    rw [sum_add_distrib, ← mul_sum, V.sum_hinge N C.X hN1 (by have := C.hX; omega)] at hsum
    have hrep : ∑ k ∈ range (C.X * N), max (C.Sk (k / r) - C.lam) 0 =
        r * ∑ k ∈ range (C.X * C.L), max (C.Sk k - C.lam) 0 := by
      rw [show C.X * N = r * (C.X * C.L) by rw [hN]; ring]
      exact V.sum_range_mul_div (fun k => max (C.Sk k - C.lam) 0) r hr0 _
    rw [hrep] at hsum
    set σ := ∑ k ∈ range (C.X * C.L), max (C.Sk k - C.lam) 0 with hσ
    set S' := ∑ k ∈ range (C.X * N), max (C.Sk (k / r) - Lsh * (k : ℝ) / N - (C.lam - Lsh)) 0
    -- `S'/N ≤ σ/L + L(N + 1)/(2N)` and `L/(2N) ≤ L/(2r) ≤ δ/2`
    have h1 : 1 / (N : ℝ) * S' ≤ 1 / C.L * σ + Lsh / 2 + Lsh / (2 * N) := by
      have : 1 / (N : ℝ) * S' ≤ 1 / (N : ℝ) * (r * σ + Lsh * (((N : ℝ) + 1) / 2)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      refine this.trans (le_of_eq ?_)
      rw [hNr]; field_simp; ring
    have h2 : Lsh / (2 * N) ≤ δ := by
      rw [div_le_iff₀ (by positivity)]
      have hrN : (r : ℝ) ≤ N := by
        have : (1 : ℝ) ≤ C.L := by exact_mod_cast hL1
        rw [hNr]; nlinarith
      have : Lsh ≤ δ * r := by rwa [div_le_iff₀ hδ, mul_comm] at hrδ
      nlinarith
    linarith

end Ti
end Chi2U
