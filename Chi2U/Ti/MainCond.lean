/-
# Theorem V_i: the main theorem, conditional on the three inputs (PROOF_TI2 §2 "§7 proof", PROOF_U §7)

**Copy of `Chi2U/MainCond.lean`** for the Ti₂ machine. `MachineBoundsT n` packages, for **even** `h`, the inputs about
`Δ_h = Ti.Delta n h` (trace `n ≥ 3`):
* `den`: positive rationals with `den h • Δ_h ∈ ℤ[X]` and `log den h ≤ (α + ε) h²` eventually
  (odd primes: Theorem A′ and Lemma S; `p = 2`: Lemma 10_ν for even `n`, Lemma 10_0 for odd `n`);
* `analytic`: `|Δ_h(T)| ≤ exp((β + ε) h²)` eventually, `T = Ti₂(z_n)` (Theorem B′_z via the shift lemma);
* `margin`: `α + β < 0`;
* `nonvan`: for each `a/b`, `Δ_h(a/b) ≠ 0` for infinitely many even `h` (Lemma P′_n, along `h = 3ℓ − 1`).
`irrational_of_boundsT` applies Lemma E (`Chi2U.Criterion`, reused) to `P h := Δ_{2⌊h/2⌋}`; the proof is the χ₂ file's
verbatim (`tendsto_evenPart` is reused from `Chi2U.MainCond`).
-/
import Chi2U.Ti.PoleExpansion
import Chi2U.Criterion

namespace Chi2U
namespace Ti

open Polynomial Filter Topology

/-- The inputs to the endgame for the `Ti₂(z_n)` machine (only even `h` are used). -/
structure MachineBoundsT (n : ℕ) [Fact (3 ≤ n)] where
  den : ℕ → ℚ
  den_pos : ∀ h, 0 < den h
  den_int : ∀ h k, ∃ z : ℤ, den h * (Delta n h).coeff k = z
  α : ℝ
  β : ℝ
  margin : α + β < 0
  arith : ∀ ε > 0, ∀ᶠ h : ℕ in atTop, Even h → Real.log (den h) ≤ (α + ε) * (h : ℝ) ^ 2
  analytic : ∀ ε > 0, ∀ᶠ h : ℕ in atTop, Even h →
    |aeval (TT n) (Delta n h)| ≤ Real.exp ((β + ε) * (h : ℝ) ^ 2)
  nonvan : ∀ (a : ℤ) (b : ℕ), 0 < b → ∃ᶠ h : ℕ in atTop, Even h ∧ (Delta n h).eval ((a : ℚ) / b) ≠ 0

variable {n : ℕ} [Fact (3 ≤ n)]

/-- **Main theorem of Theorem V_i, conditional form**: `Ti₂(z_n) ∉ ℚ` from the machine bounds. -/
theorem irrational_of_boundsT (H : MachineBoundsT n) : Irrational (Ti2 (zT n)) := by
  show Irrational (TT n)
  set s : ℝ := H.α + H.β with hs
  have hs0 : s < 0 := H.margin
  set c : ℝ := -s / 8 with hc_def
  have hc : 0 < c := by rw [hc_def]; linarith
  have hε : 0 < -s / 4 := by linarith
  refine irrational_of_poly_approx (TT n) (fun h => Delta n (2 * (h / 2)))
    (fun h => (natDegree_Delta_le _).trans (by omega)) (fun h => H.den (2 * (h / 2)))
    (fun h => H.den_pos _) (fun h k => H.den_int _ k) c hc ?_ ?_
  · have hA := tendsto_evenPart.eventually (H.arith (-s / 4) hε)
    have hB := tendsto_evenPart.eventually (H.analytic (-s / 4) hε)
    filter_upwards [hA, hB, eventually_ge_atTop 2] with h ha hb hh2
    have hev : Even (2 * (h / 2)) := even_two_mul _
    have ha' := ha hev
    have hb' := hb hev
    set N := 2 * (h / 2) with hN
    have hd : (0 : ℝ) < ((H.den N : ℚ) : ℝ) := by exact_mod_cast H.den_pos N
    have hNh : (h : ℝ) ≤ 2 * (N : ℝ) := by
      have : h ≤ 2 * N := by omega
      exact_mod_cast this
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    calc ((H.den N : ℚ) : ℝ) * |aeval (TT n) (Delta n N)|
        ≤ Real.exp ((H.α + -s / 4) * (N : ℝ) ^ 2) * Real.exp ((H.β + -s / 4) * (N : ℝ) ^ 2) := by
          gcongr
          rw [← Real.exp_log hd]
          exact Real.exp_le_exp.mpr ha'
      _ = Real.exp ((s / 2) * (N : ℝ) ^ 2) := by
          rw [← Real.exp_add]; congr 1; rw [hs]; ring
      _ ≤ Real.exp (-c * (h : ℝ) ^ 2) := by
          apply Real.exp_le_exp.mpr
          rw [hc_def]
          have : (h : ℝ) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by nlinarith
          nlinarith
  · intro a b hb
    refine (H.nonvan a b hb).mono (fun h ⟨hev, hne⟩ => ?_)
    obtain ⟨j, rfl⟩ := hev
    have : 2 * ((j + j) / 2) = j + j := by omega
    simpa [this] using hne

end Ti
end Chi2U
