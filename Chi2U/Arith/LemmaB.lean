/-
# Lemma B: the bordered identity (PROOF_U §3.3)

Here `K = h + 1 > h`, so the `K` Lagrange polynomials `f_i = D/(t − x_i)` (degree `h`) span `ℚ[t]_{≤h}`, one
dimension too many. With the `K × K` Gram matrix `G^f(X) = (Λ_X(f_i f_j))`:

    Δ_h(X) · Π_i D′(x_i) = (−1)^{K(K−1)/2} · 𝟙ᵀ adj(G^f(X)) 𝟙.

Proof: `Δ_h` is the `(h, h)` cofactor of `H_{h+1} = (Λ_X(t^{a+b}))_{a,b ≤ h}`; `G^f = C H_{h+1} Cᵀ` with `C` the
coefficient matrix of the `f_i`, whose column `h` is `𝟙` (the `f_i` are monic); `adj(H) = (det C)^{−2} Cᵀ adj(G^f) C`;
`(det C)² = (−1)^{K(K−1)/2} Π_i D′(x_i)`. The `K`-valued Hankel determinant is identified with `Δ_h` by
`LemmaR.Delta_map`.

Lean route (no division in `ℚ(√5)[X]`):
* `Λ_X` is additive (`LamX_add`), hence `ℚ`-linear (`LamX_C_mul`, via `map_rat_smul`);
* `GramF_eq`: `G^f = C' H C'ᵀ` (`C'` the coefficient matrix mapped to `ℚ(√5)[X]`);
* `sum_adjugate_GramF`: `𝟙ᵀ adj(G^f) 𝟙 = (det C)² · adj(H)_{hh}`, from `adjugate_mul_distrib`, `adj(C') C' = det C'`
  and `C' e_h = 𝟙`;
* `adjugate_last`: `adj(H)_{hh}` is the top-left `h × h` minor (Laplace along the last row);
* `det_coefM_sq`: `(det C)² = (−1)^{K(K−1)/2} Π D′(x_i)`, from `C Vᵀ = diag(D′(x_i))` (`V` the Vandermonde matrix of
  the poles) and `Π_i Π_{j≠i} (v_i − v_j) = (−1)^{n(n−1)/2} (det V)²` (`prod_prod_ite_ne`).
-/
import Chi2U.Arith.Defs

namespace Chi2U

variable {mz : ℕ} [Fact (1 ≤ mz)]

open Polynomial Finset

/-- `f_i = D/(t − x_i) = Π_{m ≠ i}(t − x_m)`. -/
noncomputable def fLag (h i : ℕ) : ℚ[X] := ∏ m ∈ (range (h + 1)).erase i, (X - C ((poleZ h m : ℤ) : ℚ))

/-- `Λ_X(g) = A(g) + X·B(g) ∈ ℚ(√5)[X]`. -/
noncomputable def LamX (mz : ℕ) [Fact (1 ≤ mz)] (h : ℕ) (g : ℚ[X]) : (Qd mz)[X] := C (Afun mz h g) + X * C (Bfun mz h g)

/-- The `K × K` Lagrange Gram matrix `G^f(X)`. -/
noncomputable def GramF (mz : ℕ) [Fact (1 ≤ mz)] (h : ℕ) : Matrix (Fin (h + 1)) (Fin (h + 1)) (Qd mz)[X] :=
  fun i j => LamX mz h (fLag h i * fLag h j)

namespace LB

/-! ### Linearity of `Λ_X` -/

lemma cPole_add (h : ℕ) (g₁ g₂ : ℚ[X]) (m : ℕ) : cPole h (g₁ + g₂) m = cPole h g₁ m + cPole h g₂ m := by
  simp [cPole, add_div]

lemma Afun_add (h : ℕ) (g₁ g₂ : ℚ[X]) : Afun mz h (g₁ + g₂) = Afun mz h g₁ + Afun mz h g₂ := by
  simp only [Afun, add_divByMonic, muPoly_add, cPole_add, Rat.cast_add, add_mul, sum_add_distrib]
  ring

lemma Bfun_add (h : ℕ) (g₁ g₂ : ℚ[X]) : Bfun mz h (g₁ + g₂) = Bfun mz h g₁ + Bfun mz h g₂ := by
  simp only [Bfun, cPole_add, Rat.cast_add, add_mul, sum_add_distrib]
  ring

lemma LamX_add (h : ℕ) (g₁ g₂ : ℚ[X]) : LamX mz h (g₁ + g₂) = LamX mz h g₁ + LamX mz h g₂ := by
  simp only [LamX, Afun_add, Bfun_add, C_add]; ring

/-- `Λ_X` as an additive map. -/
noncomputable def LamXHom (mz : ℕ) [Fact (1 ≤ mz)] (h : ℕ) : ℚ[X] →+ (Qd mz)[X] := AddMonoidHom.mk' (LamX mz h) (LamX_add h)

lemma LamXHom_apply (h : ℕ) (g : ℚ[X]) : LamXHom mz h g = LamX mz h g := rfl

lemma LamX_C_mul (h : ℕ) (c : ℚ) (g : ℚ[X]) : LamX mz h (C c * g) = C (c : (Qd mz)) * LamX mz h g := by
  have := map_rat_smul (LamXHom mz h) c g
  rw [LamXHom_apply, LamXHom_apply] at this
  rw [← smul_eq_C_mul, this, Algebra.smul_def, Polynomial.algebraMap_apply, eq_ratCast]

lemma LamX_sum {ι : Type*} (h : ℕ) (s : Finset ι) (g : ι → ℚ[X]) :
    LamX mz h (∑ i ∈ s, g i) = ∑ i ∈ s, LamX mz h (g i) :=
  map_sum (LamXHom mz h) g s

/-! ### The coefficient matrix -/

lemma fLag_monic (h i : ℕ) : (fLag h i).Monic := monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

lemma natDegree_fLag {h i : ℕ} (hi : i ≤ h) : (fLag h i).natDegree = h := by
  rw [fLag, natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _),
    sum_congr rfl (fun _ _ => natDegree_X_sub_C _), sum_const, smul_eq_mul, mul_one,
    card_erase_of_mem (mem_range.mpr (Nat.lt_succ_of_le hi)), card_range, Nat.succ_sub_one]

/-- The coefficient matrix `C_{ia} = [t^a] f_i`. -/
noncomputable def coefM (h : ℕ) : Matrix (Fin (h + 1)) (Fin (h + 1)) ℚ := Matrix.of fun i a => (fLag h i).coeff a

@[simp] lemma coefM_apply (h : ℕ) (i a : Fin (h + 1)) : coefM h i a = (fLag h i).coeff a := rfl

lemma coefM_last {h : ℕ} (i : Fin (h + 1)) : coefM h i (Fin.last h) = 1 := by
  have := (fLag_monic h i).coeff_natDegree
  rw [natDegree_fLag (Nat.lt_succ_iff.mp i.isLt)] at this
  simpa [coefM] using this

lemma fLag_eq_sum {h : ℕ} (i : Fin (h + 1)) :
    fLag h i = ∑ a : Fin (h + 1), C (coefM h i a) * X ^ (a : ℕ) := by
  simp only [coefM_apply]
  rw [Fin.sum_univ_eq_sum_range (fun a => C ((fLag h i).coeff a) * X ^ a)]
  conv_lhs => rw [as_sum_range_C_mul_X_pow (fLag h i), natDegree_fLag (Nat.lt_succ_iff.mp i.isLt)]

/-- The Hankel matrix `H_{h+1} = (Λ_X(t^{a+b}))_{a,b ≤ h}`. -/
noncomputable def Hmat (mz : ℕ) [Fact (1 ≤ mz)] (h : ℕ) : Matrix (Fin (h + 1)) (Fin (h + 1)) (Qd mz)[X] :=
  fun a b => LamX mz h (X ^ ((a : ℕ) + b))

/-- `G^f = C' H C'ᵀ`. -/
lemma GramF_eq (h : ℕ) :
    GramF mz h = (coefM h).map (algebraMap ℚ (Qd mz)[X]) * Hmat mz h * ((coefM h).map (algebraMap ℚ (Qd mz)[X])).transpose := by
  refine Matrix.ext (fun i j => ?_)
  simp only [GramF, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Hmat]
  rw [fLag_eq_sum i, fLag_eq_sum j, sum_mul_sum, LamX_sum]
  simp_rw [LamX_sum, sum_mul]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl (fun a _ => ?_)
  refine sum_congr rfl (fun b _ => ?_)
  rw [show C (coefM h i a) * X ^ (a : ℕ) * (C (coefM h j b) * X ^ (b : ℕ)) =
      C (coefM h i a * coefM h j b) * X ^ ((a : ℕ) + b) by rw [pow_add, C_mul]; ring]
  rw [LamX_C_mul, Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, eq_ratCast, eq_ratCast,
    Rat.cast_mul, C_mul]
  ring

/-! ### The adjugate -/

/-- `adj(M)_{nn}` is the top-left `n × n` minor. -/
lemma adjugate_last {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    M.adjugate (Fin.last n) (Fin.last n) = (M.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.adjugate_apply, Matrix.det_succ_row _ (Fin.last n),
    Fintype.sum_eq_single (Fin.last n)]
  · have hsub : ((M.updateRow (Fin.last n) (Pi.single (Fin.last n) 1)).submatrix (Fin.last n).succAbove
        (Fin.last n).succAbove) = M.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      simp [Fin.succAbove_last]
    rw [hsub, Matrix.updateRow_self, Pi.single_eq_same, ← two_mul, pow_mul]
    simp
  · intro j hj
    simp [Matrix.updateRow_self, hj]

/-- `𝟙ᵀ adj(G^f) 𝟙 = (det C)² adj(H)_{hh}`. -/
lemma sum_adjugate_GramF (h : ℕ) :
    ∑ a, ∑ b, (GramF mz h).adjugate a b =
      C (((coefM h).det : ℚ) : (Qd mz)) ^ 2 * (Hmat mz h).adjugate (Fin.last h) (Fin.last h) := by
  set C' := (coefM h).map (algebraMap ℚ (Qd mz)[X]) with hC'
  set one : Fin (h + 1) → (Qd mz)[X] := fun _ => 1 with hone
  set e : Fin (h + 1) → (Qd mz)[X] := Pi.single (Fin.last h) 1 with he
  have hcol : C'.mulVec e = one := by
    funext i
    simp only [he, hC', hone, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.single_apply, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, coefM_last, map_one]
  have hv : C'.adjugate.mulVec one = C'.det • e := by
    rw [← hcol, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hsum : ∀ M : Matrix (Fin (h + 1)) (Fin (h + 1)) (Qd mz)[X], ∑ a, ∑ b, M a b = one ⬝ᵥ M.mulVec one := by
    intro M
    simp [hone, dotProduct, Matrix.mulVec]
  have hdet : C'.det = C (((coefM h).det : ℚ) : (Qd mz)) := by
    rw [hC', ← RingHom.mapMatrix_apply, ← RingHom.map_det, Polynomial.algebraMap_apply, eq_ratCast]
  rw [hsum, GramF_eq, ← hC', Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
    ← Matrix.adjugate_transpose, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, hv, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, he, single_dotProduct,
    hdet]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  ring

/-! ### `(det C)²` -/

lemma prod_prod_ite_ne {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) :
    ∏ i, ∏ j, (if j = i then 1 else v i - v j) = (-1) ^ (n * (n - 1) / 2) * (Matrix.vandermonde v).det ^ 2 := by
  have hsplit : ∀ i, ∏ j, (if j = i then 1 else v i - v j) =
      (∏ j ∈ Ioi i, (-1) * (v j - v i)) * ∏ j ∈ Iio i, (v i - v j) := by
    intro i
    have hpt : ∀ j, (if j = i then 1 else v i - v j) =
        (if i < j then (-1) * (v j - v i) else 1) * (if j < i then v i - v j else 1) := by
      intro j
      rcases lt_trichotomy i j with hij | hij | hij
      · simp [hij, hij.ne', not_lt_of_gt hij]
      · simp [hij]
      · simp [hij, hij.ne, not_lt_of_gt hij]
    rw [prod_congr rfl (fun j _ => hpt j), prod_mul_distrib, ← prod_filter, ← prod_filter, filter_lt_eq_Ioi,
      filter_gt_eq_Iio]
  have hswap : ∏ i : Fin n, ∏ j ∈ Iio i, (v i - v j) = ∏ j : Fin n, ∏ i ∈ Ioi j, (v i - v j) :=
    prod_comm' (fun i j => by simp)
  have hcard : ∑ i : Fin n, #(Ioi i) = n * (n - 1) / 2 := by
    simp only [Fin.card_Ioi]
    rw [Fin.sum_univ_eq_sum_range (fun i => n - 1 - i), sum_range_reflect (fun i => i) n, sum_range_id]
  rw [prod_congr rfl (fun i _ => hsplit i), prod_mul_distrib, hswap, Matrix.det_vandermonde]
  simp only [prod_mul_distrib, prod_const, prod_pow_eq_pow_sum, hcard]
  ring

lemma poleZ_sub (h i l : ℕ) : ((poleZ h i : ℤ) : ℚ) - poleZ h l = 2 * ((i : ℚ) - l) := by
  unfold poleZ; push_cast; ring

lemma dPrime_ne_zero (h i : ℕ) : dPrime h i ≠ 0 := by
  unfold dPrime
  refine prod_ne_zero_iff.mpr (fun l _ => ?_)
  split_ifs with hl
  · exact one_ne_zero
  · rw [poleZ_sub]
    refine mul_ne_zero two_ne_zero (sub_ne_zero.mpr ?_)
    exact_mod_cast (Ne.symm hl)

/-- `f_i(x_m) = [m = i] D′(x_i)`. -/
lemma eval_fLag {h : ℕ} (i : ℕ) {m : ℕ} (hm : m ≤ h) :
    (fLag h i).eval ((poleZ h m : ℤ) : ℚ) = if m = i then dPrime h i else 0 := by
  unfold fLag
  rw [eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  split_ifs with hmi
  · subst hmi
    unfold dPrime
    rw [← mul_prod_erase (range (h + 1)) _ (mem_range.mpr (Nat.lt_succ_of_le hm)), if_pos rfl, one_mul]
    exact prod_congr rfl (fun l hl => by rw [if_neg (ne_of_mem_erase hl)])
  · exact prod_eq_zero (mem_erase.mpr ⟨hmi, mem_range.mpr (Nat.lt_succ_of_le hm)⟩) (sub_self _)

/-- The poles as a vector. -/
noncomputable def xv (h : ℕ) : Fin (h + 1) → ℚ := fun m => ((poleZ h m : ℤ) : ℚ)

lemma coefM_mul_vand (h : ℕ) :
    coefM h * (Matrix.vandermonde (xv h)).transpose = Matrix.diagonal (fun i : Fin (h + 1) => dPrime h i) := by
  ext i m
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.vandermonde_apply, coefM_apply, xv]
  rw [Fin.sum_univ_eq_sum_range (fun a => (fLag h i).coeff a * ((poleZ h m : ℤ) : ℚ) ^ a),
    ← eval_eq_sum_range' (by rw [natDegree_fLag (Nat.lt_succ_iff.mp i.isLt)]; exact Nat.lt_succ_self h),
    eval_fLag _ (Nat.lt_succ_iff.mp m.isLt), Matrix.diagonal_apply]
  by_cases him : i = m
  · subst him; simp
  · rw [if_neg (fun e => him (Fin.ext e.symm)), if_neg him]

lemma prod_dPrime_eq (h : ℕ) :
    ∏ i : Fin (h + 1), dPrime h i = (-1) ^ ((h + 1) * h / 2) * (Matrix.vandermonde (xv h)).det ^ 2 := by
  rw [show (h + 1) * h / 2 = (h + 1) * (h + 1 - 1) / 2 by simp, ← prod_prod_ite_ne (xv h)]
  refine prod_congr rfl (fun i _ => ?_)
  rw [dPrime, ← Fin.prod_univ_eq_prod_range (fun l => if l = (i : ℕ) then 1 else
    (((poleZ h i : ℤ) : ℚ) - poleZ h l))]
  refine prod_congr rfl (fun l _ => ?_)
  simp only [xv, Fin.val_inj]

/-- `(det C)² = (−1)^{K(K−1)/2} Π_i D′(x_i)`. -/
lemma det_coefM_sq (h : ℕ) :
    (coefM h).det ^ 2 = (-1) ^ ((h + 1) * h / 2) * ∏ i : Fin (h + 1), dPrime h i := by
  have h1 := congrArg Matrix.det (coefM_mul_vand h)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at h1
  have h2 := prod_dPrime_eq h
  set s : ℚ := (-1) ^ ((h + 1) * h / 2)
  have hs : s * s = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  set dV := (Matrix.vandermonde (xv h)).det
  have hP : ∏ i : Fin (h + 1), dPrime h i ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => dPrime_ne_zero h i)
  have hV : dV ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h1; exact hP h1.symm
  have hC : (coefM h).det = s * dV := by
    apply mul_right_cancel₀ hV
    rw [h1, h2]; ring
  rw [hC, h2]
  ring

end LB

/-! ### Assembly -/

open LB in
/-- **Lemma B** (bordered identity). -/
theorem lemmaB {h : ℕ} (hh : Even h) :
    (Delta mz h).map (algebraMap ℚ (Qd mz)) * C (∏ i ∈ range (h + 1), ((dPrime h i : ℚ) : (Qd mz))) =
      C ((-1) ^ ((h + 1) * h / 2)) * ∑ a, ∑ b, (GramF mz h).adjugate a b := by
  rw [sum_adjugate_GramF, adjugate_last, Delta_map hh]
  have hsub : (Hmat mz h).submatrix Fin.castSucc Fin.castSucc =
      Matrix.of fun i j : Fin h => C (Afun mz h (X ^ ((i : ℕ) + j))) + X * C (Bfun mz h (X ^ ((i : ℕ) + j))) := by
    refine Matrix.ext (fun i j => ?_)
    simp [Hmat, LamX]
  rw [hsub]
  have hsq : (((coefM h).det : ℚ) : (Qd mz)) ^ 2 =
      (-1) ^ ((h + 1) * h / 2) * ∏ i ∈ range (h + 1), ((dPrime h i : ℚ) : (Qd mz)) := by
    rw [← Rat.cast_pow, det_coefM_sq, Fin.prod_univ_eq_prod_range (fun i => dPrime h i)]
    push_cast; ring
  have hs : ((-1 : (Qd mz)[X]) ^ ((h + 1) * h / 2)) * (-1) ^ ((h + 1) * h / 2) = 1 := by
    rw [← mul_pow]; norm_num
  rw [← C_pow, hsq, C_mul, C_pow, C_neg, C_1, ← mul_assoc, ← mul_assoc, hs, one_mul, mul_comm]

end Chi2U
