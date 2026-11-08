/-
# Lemma S: Newton interpolation and the Vandermonde factor

For points `x : ι → ℤ` (`ι` linearly ordered) and a set `S` of atoms, the rows `(x_a^j)_j`, `a ∈ S`, factor as
`E · W` with `E` integral lower triangular, `det E = Π_{a ∈ S} Π_{k ∈ S, k < a} (x_a − x_k)` (the Vandermonde
product of `x_S`), and `W` integral (divided differences `W_{b j} = (t^j mod N_{S≤b})_{|S<b|}`, `N_Y = Π_{k∈Y}(t − x_k)`).
This is how the factor `det V_{S,I} = Vand(x_S)·(integral)` of PROOF_U's Lemma 7′ enters the Lean proof.

* `modByMonic_insert`, `modByMonic_newton`: the Newton form of `f mod N_Y` (over `ℤ[X]`, no division);
* `eval_newton`: `f(x_a) = Σ_{b ∈ S, b ≤ a} (f mod N_{S≤b})_{|S<b|} · Π_{k ∈ S, k < b}(x_a − x_k)` for `a ∈ S`;
* `Emat`, `W1`, `W2`, `IdS`: `E W₂ = (x_a^j)`, `E W₁ = ([a ∈ S] x_a^j)`, `E·IdS·Eᵀ = IdS`, and `det E`.
-/
import Chi2U.V.SMatrix

namespace Chi2U
namespace V
namespace LS

open Polynomial Finset

section Newton

variable {ι : Type*} [LinearOrder ι] (x : ι → ℤ)

/-- `N_Y(t) = Π_{k ∈ Y} (t − x_k)`. -/
noncomputable def nPoly (Y : Finset ι) : ℤ[X] := ∏ k ∈ Y, (X - C (x k))

lemma nPoly_monic (Y : Finset ι) : (nPoly x Y).Monic := monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

lemma natDegree_nPoly (Y : Finset ι) : (nPoly x Y).natDegree = Y.card := by
  rw [nPoly, natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _),
    sum_congr rfl (fun _ _ => natDegree_X_sub_C _)]
  simp

lemma eval_nPoly (Y : Finset ι) (t : ℤ) : (nPoly x Y).eval t = ∏ k ∈ Y, (t - x k) := by
  rw [nPoly, eval_prod]; simp

lemma eval_nPoly_eq_zero {Y : Finset ι} {a : ι} (ha : a ∈ Y) : (nPoly x Y).eval (x a) = 0 := by
  rw [eval_nPoly]; exact prod_eq_zero ha (sub_self _)

/-- A multiple of a monic `N` of degree `≤ deg N` is a constant multiple of `N`. -/
lemma eq_C_mul_of_dvd {N P : ℤ[X]} (hN : N.Monic) (hP : P.natDegree ≤ N.natDegree) (hd : N ∣ P) :
    P = C (P.coeff N.natDegree) * N := by
  obtain ⟨q, rfl⟩ := hd
  by_cases hq : q = 0
  · simp [hq]
  have hdeg := hN.natDegree_mul' hq
  have hq0 : q.natDegree = 0 := by omega
  rw [eq_C_of_natDegree_eq_zero hq0, mul_comm N, coeff_C_mul, hN.coeff_natDegree, mul_one]

lemma modByMonic_step (f : ℤ[X]) {N N' : ℤ[X]} (hN : N.Monic) (hN' : N'.Monic) (hdvd : N ∣ N')
    (hdeg : N'.natDegree = N.natDegree + 1) :
    f %ₘ N' = f %ₘ N + C ((f %ₘ N').coeff N.natDegree) * N := by
  have hd : N ∣ f %ₘ N' - f %ₘ N := by
    obtain ⟨c, hc⟩ := hdvd
    rw [modByMonic_eq_sub_mul_div f N', modByMonic_eq_sub_mul_div f N]
    exact ⟨f /ₘ N - c * (f /ₘ N'), by rw [hc]; ring⟩
  have h1 : (f %ₘ N').natDegree ≤ N.natDegree := by
    have := natDegree_modByMonic_lt f hN' (fun e => by rw [e, natDegree_one] at hdeg; omega)
    omega
  have h2 : (f %ₘ N).natDegree ≤ N.natDegree := natDegree_modByMonic_le f hN
  have key := eq_C_mul_of_dvd hN ((natDegree_sub_le _ _).trans (max_le h1 h2)) hd
  have hc0 : (f %ₘ N).coeff N.natDegree = 0 := by
    refine coeff_eq_zero_of_degree_lt ?_
    have := degree_modByMonic_lt f hN
    rwa [degree_eq_natDegree hN.ne_zero] at this
  rw [coeff_sub, hc0, sub_zero] at key
  rw [← key]; ring

lemma modByMonic_insert (f : ℤ[X]) {a : ι} {Y : Finset ι} (ha : a ∉ Y) :
    f %ₘ nPoly x (insert a Y) =
      f %ₘ nPoly x Y + C ((f %ₘ nPoly x (insert a Y)).coeff Y.card) * nPoly x Y := by
  have := modByMonic_step f (nPoly_monic x Y) (nPoly_monic x (insert a Y))
    (prod_dvd_prod_of_subset _ _ _ (subset_insert a Y))
    (by rw [natDegree_nPoly, natDegree_nPoly, card_insert_of_notMem ha])
  rwa [natDegree_nPoly] at this

/-- Newton form of `f mod N_Y`. -/
lemma modByMonic_newton (f : ℤ[X]) (Y : Finset ι) :
    f %ₘ nPoly x Y = ∑ k ∈ Y, C ((f %ₘ nPoly x (Y.filter (· ≤ k))).coeff (Y.filter (· < k)).card) *
      nPoly x (Y.filter (· < k)) := by
  induction Y using Finset.induction_on_max with
  | empty => simp [nPoly]
  | insert a Y hlt ih =>
      have haY : a ∉ Y := fun h => lt_irrefl a (hlt a h)
      have e1 : (insert a Y).filter (· ≤ a) = insert a Y :=
        filter_true_of_mem (fun k hk => by
          rcases mem_insert.mp hk with rfl | h
          · exact le_rfl
          · exact (hlt k h).le)
      have e2 : (insert a Y).filter (· < a) = Y := by
        rw [filter_insert, if_neg (lt_irrefl a)]
        exact filter_true_of_mem (fun k hk => hlt k hk)
      have e3 : ∀ k ∈ Y, (insert a Y).filter (· ≤ k) = Y.filter (· ≤ k) := fun k hk => by
        rw [filter_insert, if_neg (not_le.mpr (hlt k hk))]
      have e4 : ∀ k ∈ Y, (insert a Y).filter (· < k) = Y.filter (· < k) := fun k hk => by
        rw [filter_insert, if_neg (not_lt.mpr (hlt k hk).le)]
      rw [sum_insert haY, e1, e2]
      conv_lhs => rw [modByMonic_insert x f haY, ih]
      rw [add_comm]
      congr 1
      exact sum_congr rfl (fun k hk => by rw [e3 k hk, e4 k hk])

/-- Newton interpolation at a node. -/
lemma eval_newton (f : ℤ[X]) (S : Finset ι) {a : ι} (ha : a ∈ S) :
    ∑ b ∈ S.filter (· ≤ a), (f %ₘ nPoly x (S.filter (· ≤ b))).coeff (S.filter (· < b)).card *
      ∏ k ∈ S.filter (· < b), (x a - x k) = f.eval (x a) := by
  set Y := S.filter (· ≤ a) with hY
  have haY : a ∈ Y := mem_filter.mpr ⟨ha, le_rfl⟩
  have hf : f.eval (x a) = (f %ₘ nPoly x Y).eval (x a) := by
    conv_lhs => rw [← modByMonic_add_div f (nPoly x Y)]
    rw [eval_add, eval_mul, eval_nPoly_eq_zero x haY, zero_mul, add_zero]
  rw [hf, modByMonic_newton, eval_finsetSum]
  refine sum_congr rfl (fun b hb => ?_)
  have hba : b ≤ a := (mem_filter.mp hb).2
  have e1 : Y.filter (· ≤ b) = S.filter (· ≤ b) := by
    rw [hY, filter_filter]
    exact filter_congr (fun k _ => ⟨fun h => h.2, fun h => ⟨h.trans hba, h⟩⟩)
  have e2 : Y.filter (· < b) = S.filter (· < b) := by
    rw [hY, filter_filter]
    exact filter_congr (fun k _ => ⟨fun h => h.2, fun h => ⟨(le_of_lt h).trans hba, h⟩⟩)
  rw [eval_mul, eval_C, eval_nPoly, e1, e2]

end Newton

section Mats

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (x : ι → ℤ) (S : Finset ι)

/-- The lower triangular Newton matrix `E`. -/
def Emat : Matrix ι ι ℤ := fun a b =>
  if a ∈ S ∧ b ∈ S ∧ b ≤ a then ∏ k ∈ S.filter (· < b), (x a - x k) else if a = b then 1 else 0

/-- Divided differences `W_{b j} = (t^j mod N_{S≤b})_{|S<b|}`. -/
noncomputable def ddW (b : ι) (j : ℕ) : ℤ :=
  ((X ^ j : ℤ[X]) %ₘ nPoly x (S.filter (· ≤ b))).coeff (S.filter (· < b)).card

noncomputable def W1 (h : ℕ) : Matrix ι (Fin h) ℤ := fun b j => if b ∈ S then ddW x S b j else 0

noncomputable def W2 (h : ℕ) : Matrix ι (Fin h) ℤ := fun b j => if b ∈ S then ddW x S b j else x b ^ (j : ℕ)

def IdS : Matrix ι ι ℤ := Matrix.diagonal fun a => if a ∈ S then 0 else 1

lemma Emat_of_notMem {a b : ι} (hb : b ∉ S) : Emat x S a b = if a = b then 1 else 0 := by
  unfold Emat; rw [if_neg (fun h => hb h.2.1)]

lemma Emat_of_notMem_left {a b : ι} (ha : a ∉ S) : Emat x S a b = if a = b then 1 else 0 := by
  unfold Emat; rw [if_neg (fun h => ha h.1)]

/-- Row `a ∈ S` of `E` against any column agreeing with the divided differences on `S`. -/
lemma Emat_row_mem {a : ι} (ha : a ∈ S) (j : ℕ) (g : ι → ℤ) (hg : ∀ b ∈ S, g b = ddW x S b j) :
    ∑ b, Emat x S a b * g b = x a ^ j := by
  have h1 : ∀ b, Emat x S a b * g b =
      if b ∈ S.filter (· ≤ a) then (∏ k ∈ S.filter (· < b), (x a - x k)) * ddW x S b j else 0 := by
    intro b
    unfold Emat
    by_cases hb : b ∈ S ∧ b ≤ a
    · rw [if_pos ⟨ha, hb.1, hb.2⟩, if_pos (mem_filter.mpr hb), hg b hb.1]
    · rw [if_neg (fun h => hb ⟨h.2.1, h.2.2⟩), if_neg (fun h => hb (mem_filter.mp h))]
      by_cases hab : a = b
      · subst hab; exact absurd ⟨ha, le_rfl⟩ hb
      · rw [if_neg hab, zero_mul]
  rw [sum_congr rfl (fun b _ => h1 b), ← sum_filter, filter_mem_eq_inter, univ_inter]
  have := eval_newton x ((X : ℤ[X]) ^ j) S ha
  rw [eval_pow, eval_X] at this
  rw [← this]
  exact sum_congr rfl (fun b _ => by unfold ddW; ring)

lemma Emat_row_notMem {a : ι} (ha : a ∉ S) (g : ι → ℤ) : ∑ b, Emat x S a b * g b = g a := by
  rw [sum_congr rfl (fun b _ => by rw [Emat_of_notMem_left x S ha])]
  simp

lemma Emat_mul_W2 (h : ℕ) : Emat x S * W2 x S h = Matrix.of fun a (j : Fin h) => x a ^ (j : ℕ) := by
  ext a j
  rw [Matrix.mul_apply, Matrix.of_apply]
  by_cases ha : a ∈ S
  · exact Emat_row_mem x S ha j (fun b => W2 x S h b j) (fun b hb => by simp [W2, hb])
  · rw [Emat_row_notMem x S ha (fun b => W2 x S h b j)]; simp [W2, ha]

lemma Emat_mul_W1 (h : ℕ) :
    Emat x S * W1 x S h = Matrix.of fun a (j : Fin h) => if a ∈ S then x a ^ (j : ℕ) else 0 := by
  ext a j
  rw [Matrix.mul_apply, Matrix.of_apply]
  by_cases ha : a ∈ S
  · rw [if_pos ha]
    exact Emat_row_mem x S ha j (fun b => W1 x S h b j) (fun b hb => by simp [W1, hb])
  · rw [Emat_row_notMem x S ha (fun b => W1 x S h b j)]; simp [W1, ha]

lemma Emat_IdS : Emat x S * IdS S * (Emat x S).transpose = IdS S := by
  ext a c
  rw [IdS, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  rw [sum_congr rfl (fun b _ => show Emat x S a b * (if b ∈ S then 0 else 1) * Emat x S c b =
      if b ∈ S then 0 else (if a = b then 1 else 0) * (if c = b then 1 else 0) by
    by_cases hb : b ∈ S
    · simp [hb]
    · rw [if_neg hb, if_neg hb, Emat_of_notMem x S hb, Emat_of_notMem x S hb, mul_one])]
  rw [Matrix.diagonal_apply]
  by_cases hac : a = c
  · subst hac
    rw [sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp), if_pos rfl]
    by_cases ha : a ∈ S <;> simp [ha]
  · rw [if_neg hac]
    refine sum_eq_zero (fun b _ => ?_)
    by_cases hb : b ∈ S
    · simp [hb]
    · rw [if_neg hb]
      by_cases hab : a = b
      · subst hab; simp [Ne.symm hac]
      · simp [hab]

lemma det_Emat : (Emat x S).det = ∏ a ∈ S, ∏ k ∈ S.filter (· < a), (x a - x k) := by
  rw [Matrix.det_of_isLowerTriangular (Emat x S) (fun i j hij => ?_)]
  · rw [← prod_filter_mul_prod_filter_not univ (· ∈ S)]
    rw [prod_eq_one (s := univ.filter (· ∉ S)) (fun a ha => by
      rw [Emat_of_notMem_left x S (mem_filter.mp ha).2, if_pos rfl])]
    rw [mul_one, filter_mem_eq_inter, univ_inter]
    exact prod_congr rfl (fun a ha => by unfold Emat; rw [if_pos ⟨ha, ha, le_rfl⟩])
  · have hij' : i < j := hij
    unfold Emat
    rw [if_neg (fun h => absurd h.2.2 (not_le.mpr hij')), if_neg (ne_of_lt hij')]

end Mats

end LS
end V
end Chi2U
