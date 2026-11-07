/-
# Determinants of sums of rank-one matrices (Andreief / Cauchy–Binet)

For `M = Σ_k c_k x_k y_kᵀ` (finite index type `ι`, square index type `n`):
* `det_sum_rankOne_rows`: `det M = Σ_{f : n → ι} (∏_i c_{f i} x_{f i}(i)) · det(y_{f i}(j))`;
* `factorial_smul_det_sum_rankOne`: `(#n)! · det M = Σ_{f : n → ι} (∏_i c_{f i}) · det(x_{f i}(j)) · det(y_{f i}(j))`.
The second (symmetric) form is used for the node expansion of Theorem B and for `q`-adic slot expansions.
(Copied verbatim from `lean_chi2/Chi2Irrational/Analytic/Andreief.lean`, namespace renamed `Chi2Irr` → `Chi2U`.)
-/
import Mathlib

namespace Chi2U

open Matrix Finset Equiv

variable {R : Type*} [CommRing R] {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- Row expansion of `det (Σ_k c_k x_k y_kᵀ)`. -/
lemma det_sum_rankOne_rows (c : ι → R) (x y : ι → n → R) :
    (Matrix.of fun i j => ∑ k, c k * x k i * y k j).det =
      ∑ f : n → ι, (∏ i, (c (f i) * x (f i) i)) * (Matrix.of fun i j => y (f i) j).det := by
  have hrows : (Matrix.of fun i j => ∑ k, c k * x k i * y k j) =
      fun i => ∑ k, (c k * x k i) • y k := by
    ext i j
    simp [Finset.sum_apply, smul_eq_mul]
  rw [hrows]
  change (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R) (fun i => ∑ k, (c k * x k i) • y k) = _
  have h := (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).toMultilinearMap.map_sum
    (fun i k => (c k * x k i) • y k)
  rw [AlternatingMap.coe_multilinearMap] at h
  rw [h]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  have h2 := (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).toMultilinearMap.map_smul_univ
    (fun i => c (f i) * x (f i) i) (fun i => y (f i))
  rw [AlternatingMap.coe_multilinearMap] at h2
  rw [h2, smul_eq_mul]
  rfl

/-- **Andreief's identity** (the symmetric Cauchy–Binet form). -/
theorem factorial_smul_det_sum_rankOne (c : ι → R) (x y : ι → n → R) :
    (Fintype.card n).factorial • (Matrix.of fun i j => ∑ k, c k * x k i * y k j).det =
      ∑ f : n → ι, (∏ i, c (f i)) * (Matrix.of fun i j => x (f i) j).det *
        (Matrix.of fun i j => y (f i) j).det := by
  set M := (Matrix.of fun i j => ∑ k, c k * x k i * y k j)
  -- for each permutation, reindex the row expansion
  have hσ : ∀ σ : Perm n, M.det = ∑ f : n → ι, (∏ i, c (f i)) * (Matrix.of fun i j => y (f i) j).det *
      ((Perm.sign σ : ℤ) * ∏ i, x (f (σ i)) i) := by
    intro σ
    rw [det_sum_rankOne_rows]
    rw [← (Equiv.arrowCongr σ (Equiv.refl ι)).symm.sum_comp]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    simp only [Equiv.arrowCongr_symm, Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.coe_refl,
      Function.comp_apply, Function.id_comp, id_eq, Equiv.symm_symm]
    have hdet : (Matrix.of fun i j => y (f (σ i)) j).det =
        (Perm.sign σ : ℤ) * (Matrix.of fun i j => y (f i) j).det := by
      rw [← det_permute σ (Matrix.of fun i j => y (f i) j)]
      rfl
    rw [hdet, Finset.prod_mul_distrib]
    have hc : ∏ i, c (f (σ i)) = ∏ i, c (f i) := Equiv.prod_comp σ (fun i => c (f i))
    rw [hc]
    ring
  -- sum over all permutations
  have hsum : (Fintype.card n).factorial • M.det = ∑ σ : Perm n, M.det := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm]
  rw [hsum, Finset.sum_congr rfl (fun σ _ => hσ σ), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  rw [← Finset.mul_sum, mul_assoc, mul_assoc]
  congr 1
  rw [mul_comm]
  congr 1
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Units.smul_def, zsmul_eq_mul]
  rfl

end Chi2U
