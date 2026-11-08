/-
# Theorem B′: the truncations converge (Lemma 1′)

`LamMat_hasSum`: the node terms of `NodesU.lean` sum to `Λ(u^{i+j})` (Lemma 1′, `PoleExpansion.lemma1`);
`abs_Delta_le_of`: a uniform bound on `|det HT T|` bounds `|Δ_h(T)|` (via `aeval_chi2_Delta`).
(Split from `NodesU.lean` so that the node machinery does not depend on `PoleExpansion.lean`.)
-/
import Chi2U.PoleExpansion
import Chi2U.Analytic.NodesU

namespace Chi2U

variable {mz : ℕ} [Fact (1 ≤ mz)]

open Polynomial Finset Filter Topology Matrix

/-- The Hankel matrix `Λ(u^{i+j})`. -/
noncomputable def LamMat (mz : ℕ) [Fact (1 ≤ mz)] (h : ℕ) : Matrix (Fin h) (Fin h) ℝ :=
  Matrix.of fun i j => LamR mz h ((X : ℚ[X]) ^ ((i : ℕ) + j))

lemma LamMat_hasSum {h : ℕ} (hh : Even h) (i j : Fin h) :
    HasSum (fun t => nodeTerm mz h ((i : ℕ) + j) t) (LamMat mz h i j) := by
  simp only [LamMat, Matrix.of_apply]
  rw [LamR_eq hh]
  convert lemma1 hh ((X : ℚ[X]) ^ ((i : ℕ) + j)) using 1
  ext t
  rw [deriv_pow_phi hh]
  unfold nodeTerm
  ring

lemma tendsto_det_HT {h : ℕ} (hh : Even h) :
    Tendsto (fun T => (HT mz h T).det) atTop (𝓝 (LamMat mz h).det) := by
  have hmat : Tendsto (fun T => HT mz h T) atTop (𝓝 (LamMat mz h)) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => (LamMat_hasSum hh i j).tendsto_sum_nat
  exact ((continuous_id.matrix_det).tendsto _).comp hmat

/-- A uniform bound on the truncations bounds `|Δ_h(T)|`. -/
theorem abs_Delta_le_of {h : ℕ} (hh : Even h) {B : ℝ} (hB : ∀ T, |(HT mz h T).det| ≤ B) :
    |aeval (TU mz) (Delta mz h)| ≤ B := by
  rw [aeval_chi2_Delta hh]
  exact le_of_tendsto' ((continuous_abs.tendsto _).comp (tendsto_det_HT hh)) hB

end Chi2U
