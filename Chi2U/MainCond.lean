/-
# The main theorem, conditional on the three inputs (PROOF_U §7)

`MachineBoundsU` packages, for **even** `h`, the inputs about `Δ_h = Delta h`:
* `den`: positive rationals with `den h • Δ_h ∈ ℤ[X]` and `log den h ≤ (α + ε) h²` eventually
  (odd primes: Lemmas 8′, 8A′, 9′ and Theorem A′; `p = 2`: Lemma 10′);
* `analytic`: `|Δ_h(T)| ≤ exp((β + ε) h²)` eventually (Theorem B′ with a dual certificate);
* `margin`: `α + β < 0`;
* `nonvan`: for each `a/b`, `Δ_h(a/b) ≠ 0` for infinitely many even `h` (Lemma P′, along `h = 3ℓ − 1`).
`irrational_of_boundsU` applies Lemma E (`Criterion.lean`, verbatim from lean_chi2) to `P h := Δ_{2⌊h/2⌋}`.
-/
import Chi2U.PoleExpansion
import Chi2U.Criterion

namespace Chi2U

open Polynomial Filter Topology

/-- The inputs to the endgame for the `χ₂(√5 − 2)` machine (only even `h` are used). -/
structure MachineBoundsU where
  den : ℕ → ℚ
  den_pos : ∀ h, 0 < den h
  den_int : ∀ h k, ∃ z : ℤ, den h * (Delta h).coeff k = z
  α : ℝ
  β : ℝ
  margin : α + β < 0
  arith : ∀ ε > 0, ∀ᶠ h : ℕ in atTop, Even h → Real.log (den h) ≤ (α + ε) * (h : ℝ) ^ 2
  analytic : ∀ ε > 0, ∀ᶠ h : ℕ in atTop, Even h →
    |aeval TU (Delta h)| ≤ Real.exp ((β + ε) * (h : ℝ) ^ 2)
  nonvan : ∀ (a : ℤ) (b : ℕ), 0 < b → ∃ᶠ h : ℕ in atTop, Even h ∧ (Delta h).eval ((a : ℚ) / b) ≠ 0

lemma tendsto_evenPart : Tendsto (fun h : ℕ => 2 * (h / 2)) atTop atTop :=
  tendsto_atTop_atTop.mpr fun b => ⟨b + 1, fun h hh => by omega⟩

/-- **Main theorem, conditional form.** -/
theorem irrational_of_boundsU (H : MachineBoundsU) : Irrational TU := by
  set s : ℝ := H.α + H.β with hs
  have hs0 : s < 0 := H.margin
  set c : ℝ := -s / 8 with hc_def
  have hc : 0 < c := by rw [hc_def]; linarith
  have hε : 0 < -s / 4 := by linarith
  refine irrational_of_poly_approx TU (fun h => Delta (2 * (h / 2)))
    (fun h => (natDegree_Delta_le _).trans (by omega)) (fun h => H.den (2 * (h / 2)))
    (fun h => H.den_pos _) (fun h k => H.den_int _ k) c hc ?_ ?_
  · have hA := tendsto_evenPart.eventually (H.arith (-s / 4) hε)
    have hB := tendsto_evenPart.eventually (H.analytic (-s / 4) hε)
    filter_upwards [hA, hB, eventually_ge_atTop 2] with h ha hb hh2
    have hev : Even (2 * (h / 2)) := even_two_mul _
    have ha' := ha hev
    have hb' := hb hev
    set n := 2 * (h / 2) with hn
    have hd : (0 : ℝ) < ((H.den n : ℚ) : ℝ) := by exact_mod_cast H.den_pos n
    have hnh : (h : ℝ) ≤ 2 * (n : ℝ) := by
      have : h ≤ 2 * n := by omega
      exact_mod_cast this
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    calc ((H.den n : ℚ) : ℝ) * |aeval TU (Delta n)|
        ≤ Real.exp ((H.α + -s / 4) * (n : ℝ) ^ 2) * Real.exp ((H.β + -s / 4) * (n : ℝ) ^ 2) := by
          gcongr
          rw [← Real.exp_log hd]
          exact Real.exp_le_exp.mpr ha'
      _ = Real.exp ((s / 2) * (n : ℝ) ^ 2) := by
          rw [← Real.exp_add]; congr 1; rw [hs]; ring
      _ ≤ Real.exp (-c * (h : ℝ) ^ 2) := by
          apply Real.exp_le_exp.mpr
          rw [hc_def]
          have : (h : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith
          nlinarith
  · intro a b hb
    refine (H.nonvan a b hb).mono (fun h ⟨hev, hne⟩ => ?_)
    obtain ⟨j, rfl⟩ := hev
    have : 2 * ((j + j) / 2) = j + j := by omega
    simpa [this] using hne

end Chi2U
