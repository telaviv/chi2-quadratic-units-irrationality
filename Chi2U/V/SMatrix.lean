/-
# Lemma S, generic matrix tools

* `det_expand_rows`: multilinearity of `det` in a set `s` of rows, each of the form `a r • u r + w r`:
  `det M = Σ_{T ⊆ s} (Π_{r ∈ T} a r) · det(M with rows r ∈ T ↦ u r, r ∈ s ∖ T ↦ w r)`.
  This replaces the Laplace/Cauchy–Binet expansion of PROOF_U's Lemma 7′.
* `vGeX_det_rc`: Leibniz with row and column exponents, `v(M_ij) ≥ ρ_i + κ_j ⇒ v(det M) ≥ Σρ + Σκ`, for any
  finite index type.
-/
import Chi2U.V.Defs

namespace Chi2U
namespace V

open Polynomial Finset

/-- Row expansion of the determinant over the subsets of a set of rows. -/
theorem det_expand_rows {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (s : Finset n) (a : n → R) (u w : n → n → R) (M : Matrix n n R)
    (hM : ∀ r ∈ s, M r = a r • u r + w r) :
    M.det = ∑ T ∈ s.powerset, (∏ r ∈ T, a r) *
      (Matrix.of fun r => if r ∈ T then u r else if r ∈ s then w r else M r).det := by
  induction s using Finset.induction_on generalizing M with
  | empty =>
      simp only [powerset_empty, sum_singleton, prod_empty, one_mul, notMem_empty, ite_false]
      rfl
  | insert r₀ s hr₀ ih =>
      rw [sum_powerset_insert hr₀]
      have hM0 := hM r₀ (mem_insert_self _ _)
      have hsplit : M.det = a r₀ * (M.updateRow r₀ (u r₀)).det + (M.updateRow r₀ (w r₀)).det := by
        conv_lhs => rw [← Matrix.updateRow_eq_self M r₀, hM0]
        rw [Matrix.det_updateRow_add, Matrix.det_updateRow_smul]
      have hu : ∀ r ∈ s, M.updateRow r₀ (u r₀) r = a r • u r + w r := fun r hr => by
        rw [Matrix.updateRow_ne (fun e => hr₀ (by rw [← e]; exact hr))]; exact hM r (mem_insert_of_mem hr)
      have hw : ∀ r ∈ s, M.updateRow r₀ (w r₀) r = a r • u r + w r := fun r hr => by
        rw [Matrix.updateRow_ne (fun e => hr₀ (by rw [← e]; exact hr))]; exact hM r (mem_insert_of_mem hr)
      rw [hsplit, ih _ hu, ih _ hw, add_comm, mul_sum]
      congr 1
      · refine sum_congr rfl (fun T hT => ?_)
        have hT0 : r₀ ∉ T := fun h => hr₀ (mem_powerset.mp hT h)
        have hmat : (Matrix.of fun r => if r ∈ T then u r else if r ∈ s then w r else M.updateRow r₀ (w r₀) r) =
            Matrix.of fun r => if r ∈ T then u r else if r ∈ insert r₀ s then w r else M r := by
          ext r c
          simp only [Matrix.of_apply, mem_insert]
          by_cases h1 : r = r₀
          · subst h1; simp [hT0, hr₀]
          · simp [h1]
        rw [hmat]
      · refine sum_congr rfl (fun T hT => ?_)
        have hT0 : r₀ ∉ T := fun h => hr₀ (mem_powerset.mp hT h)
        have hmat : (Matrix.of fun r => if r ∈ T then u r else if r ∈ s then w r else M.updateRow r₀ (u r₀) r) =
            Matrix.of fun r => if r ∈ insert r₀ T then u r else if r ∈ insert r₀ s then w r else M r := by
          ext r c
          simp only [Matrix.of_apply, mem_insert]
          by_cases h1 : r = r₀
          · subst h1; simp [hT0, hr₀]
          · simp [h1]
        rw [prod_insert hT0, hmat]
        ring

section VGe

variable {mz : ℕ} [Fact (1 ≤ mz)] {p : ℕ} [Fact p.Prime]

/-- Leibniz with row and column exponents, any finite index type. -/
theorem vGeX_det_rc {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n (Qd mz)[X]) (ρ κ : n → ℤ)
    (h : ∀ i j, vGeX p (ρ i + κ j) (M i j)) : vGeX p (∑ i, ρ i + ∑ j, κ j) M.det := by
  rw [Matrix.det_apply]
  refine vGeX_sum _ _ (fun σ _ => ?_)
  have hprod : vGeX p (∑ i, (ρ (σ i) + κ i)) (∏ i, M (σ i) i) := vGeX_prod _ _ _ (fun i _ => h (σ i) i)
  rw [sum_add_distrib, Equiv.sum_comp σ ρ] at hprod
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
  · simpa using hprod
  · simpa using vGeX_neg hprod

lemma vGeX_mono {n m : ℤ} (hmn : m ≤ n) {F : (Qd mz)[X]} (hF : vGeX p n F) : vGeX p m F :=
  fun k => vGe_mono hmn (hF k)

lemma vGeX_zero (n : ℤ) : vGeX p n (0 : (Qd mz)[X]) := fun k => by
  simpa using vGe_zero (mz := mz) (p := p) n

lemma vGeX_intCast (z : ℤ) : vGeX p 0 ((z : (Qd mz)[X])) := by
  rw [← C_eq_intCast]; exact vGeX_C (vGe_of_pInt (pInt_intCast z))

lemma vGeX_X : vGeX p 0 (X : (Qd mz)[X]) := by
  simpa using vGeX_X_mul (vGeX_one (mz := mz) (p := p))

end VGe

end V
end Chi2U
