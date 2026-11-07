/-
# `p = 2`: Lemma 10′ (PROOF_U §4)

Rescale `τ = t/2`: atoms `τ = s + ½`, poles `ξ_k = k − J`, `D(t) = 2^K D̃(τ)`, and
`Λ̃(g) := 2^{K+1} Λ(g(t/2))` satisfies `Λ(t^m) = 2^{m−K−1} Λ̃(τ^m)`. In the anchored basis
`a_i = Π_{l<i}(τ − ξ_l)`, `b_j = Π_{l<j}(τ − ξ_{K−1−l})` (a unitriangular change),
`det(Λ̃_X(a_i b_j)) = Δ̃_h = 2^{3h} Δ_h` (`det_anchored`), and with `π = i + j − K`, `N₀ = K − 1 − i − j`:
* (L) `π ≥ 1`: `v₂(G_{ij}) ≥ −π − ⌊log₂ π⌋ − 2`; `π = 0`: `G_{ij} = 0`;
* (U) `N₀ ≥ 1`: `v₂(G_{ij}) ≥ N₀ − ⌊log₂ N₀⌋`; `N₀ = 0`: `v₂(G_{ij}) ≥ 2`.
Hence `n₂ ≤ h⌊log₂ h⌋ + 3h` (`padicNorm_Delta_two`). The mechanism is `v₂(1 − z²) = v₂(4z) = 2`.

The definitions `xiPole`, `aAnch`, `bAnch`, `GA`, `GB` live in `Arith/TwoAdicDefs.lean`; the entry computations in
`Arith/TwoAdicEntries.lean`, the finite-difference and Mahler-coefficient valuations in `Arith/TwoAdicBasis.lean`.
Proof of `det_anchored`: `G = 2^{h+2}·(C_a H C_bᵀ)` with `H = (Λ_X(t^{d+e}))` and `C_a, C_b` the (lower triangular)
coefficient matrices of `a_i(t/2)`, `b_j(t/2)`, diagonal `2^{−i}`, `2^{−j}`; `det H = Δ_h` is Corollary R
(`LemmaR.Delta_map`). Proof of `padicNorm_Delta_two`: every entry has `v₂ ≥ (h − 1 − ⌊log₂ h⌋ − i) + (−j)`, Leibniz
gives `v₂(det G) ≥ −h⌊log₂ h⌋`, and `Δ_h = 2^{−3h} det G`.
-/
import Chi2U.Arith.TwoAdicEntries

namespace Chi2U

open Polynomial Finset TwoAdicAux

/-! ### The Gram identity and `det_anchored` -/

namespace TwoAdicAux

/-- `Λ_X(g) = A(g) + X·B(g) ∈ ℚ(√5)[X]`. -/
noncomputable def LamQ (h : ℕ) (g : ℚ[X]) : Q5[X] := C (Afun h g) + X * C (Bfun h g)

lemma LamQ_add (h : ℕ) (f g : ℚ[X]) : LamQ h (f + g) = LamQ h f + LamQ h g := by
  unfold LamQ; rw [Afun_add, Bfun_add, C_add, C_add]; ring

lemma LamQ_C_mul (h : ℕ) (c : ℚ) (g : ℚ[X]) : LamQ h (C c * g) = C (c : Q5) * LamQ h g := by
  unfold LamQ; rw [Afun_C_mul, Bfun_C_mul, C_mul, C_mul]; ring

lemma LamQ_sum (h : ℕ) {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    LamQ h (∑ i ∈ s, f i) = ∑ i ∈ s, LamQ h (f i) :=
  map_sum (AddMonoidHom.mk' (LamQ h) (LamQ_add h)) f s

/-- `ℚ → ℚ(√5)[X]`. -/
noncomputable def psiQ5 : ℚ →+* Q5[X] := C.comp (algebraMap ℚ Q5)

lemma psiQ_apply (r : ℚ) : psiQ5 r = C (r : Q5) := by simp [psiQ5]

/-- Coefficient matrix `(e_k)_d`. -/
noncomputable def CoefM {h : ℕ} (e : Fin h → ℚ[X]) : Matrix (Fin h) (Fin h) ℚ := fun k d => (e k).coeff d

lemma expand_fin {h : ℕ} (e : Fin h → ℚ[X]) (he : ∀ i, (e i).natDegree < h) (k : Fin h) :
    e k = ∑ d : Fin h, C (CoefM e k d) * X ^ (d : ℕ) := by
  show e k = ∑ d : Fin h, C ((e k).coeff d) * X ^ (d : ℕ)
  rw [Fin.sum_univ_eq_sum_range (fun d => C ((e k).coeff d) * X ^ d) h]
  exact as_sum_range_C_mul_X_pow' _ (he k)

/-- The monomial matrix `H_{de} = Λ_X(t^{d+e})`. -/
noncomputable def HQ (h : ℕ) : Matrix (Fin h) (Fin h) Q5[X] := fun d e => LamQ h (X ^ ((d : ℕ) + e))

theorem gram_eq {h : ℕ} (a b : Fin h → ℚ[X]) (ha : ∀ i, (a i).natDegree < h) (hb : ∀ i, (b i).natDegree < h) :
    Matrix.of (fun i j => LamQ h (a i * b j)) =
      (CoefM a).map psiQ5 * HQ h * ((CoefM b).map psiQ5).transpose := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [expand_fin a ha i, expand_fin b hb j, sum_mul_sum, LamQ_sum]
  simp only [LamQ_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun e _ => ?_)
  rw [sum_mul]
  refine sum_congr rfl (fun d _ => ?_)
  have : C (CoefM a i d) * X ^ (d : ℕ) * (C (CoefM b j e) * X ^ (e : ℕ)) =
      C (CoefM a i d * CoefM b j e) * X ^ ((d : ℕ) + e) := by
    rw [C_mul, pow_add]; ring
  rw [this, LamQ_C_mul, psiQ_apply, psiQ_apply, Rat.cast_mul, C_mul]
  simp only [HQ]
  ring

lemma det_map_psiQ {h : ℕ} (M : Matrix (Fin h) (Fin h) ℚ) : (M.map psiQ5).det = psiQ5 M.det :=
  (RingHom.map_det psiQ5 M).symm

lemma det_CoefM {h : ℕ} (e : Fin h → ℚ[X]) (hdeg : ∀ i, (e i).natDegree = i) :
    (CoefM e).det = ∏ i, (e i).leadingCoeff := by
  rw [Matrix.det_of_isLowerTriangular]
  · refine prod_congr rfl (fun i _ => ?_)
    show (e i).coeff i = _
    rw [leadingCoeff, hdeg]
  · intro i d hid
    exact coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hid)

lemma natDegree_lead_C_mul_PZ {h : ℕ} (c : ℚ) (hc : c ≠ 0) (s : Finset ℕ) :
    (C c * PZ h s).natDegree = s.card ∧ (C c * PZ h s).leadingCoeff = c := by
  refine ⟨by rw [natDegree_C_mul hc, natDegree_PZ], ?_⟩
  rw [leadingCoeff_mul, leadingCoeff_C, (PZ_monic h s).leadingCoeff, mul_one]

lemma scalar_eq (h : ℕ) :
    ((2 : ℚ) ^ (h + 2)) ^ h * (∏ i : Fin h, (1 / 2 : ℚ) ^ (i : ℕ)) ^ 2 = 2 ^ (3 * h) := by
  rw [prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => i) h, ← pow_mul, ← pow_mul,
    Finset.sum_range_id_mul_two]
  have e : (h + 2) * h = h * (h - 1) + 3 * h := by
    rcases h with _ | k
    · simp
    · simp only [Nat.add_sub_cancel]; ring
  rw [e, pow_add, one_div_pow]
  have : (2 : ℚ) ^ (h * (h - 1)) ≠ 0 := by positivity
  field_simp

end TwoAdicAux

/-- Rescaling and the unitriangular change of basis: `det G = 2^{3h} Δ_h`. -/
theorem det_anchored {h : ℕ} (hh : Even h) :
    (Matrix.of fun i j : Fin h => C (GA h i j) + X * C (GB h i j)).det =
      C ((2 : Q5) ^ (3 * h)) * (Delta h).map (algebraMap ℚ Q5) := by
  set a : Fin h → ℚ[X] := fun i => (aAnch h i).comp (C (1 / 2) * X) with ha
  set b : Fin h → ℚ[X] := fun j => (bAnch h j).comp (C (1 / 2) * X) with hb
  have hA : ∀ i : Fin h, (a i).natDegree = i ∧ (a i).leadingCoeff = (1 / 2) ^ (i : ℕ) := fun i => by
    have := natDegree_lead_C_mul_PZ (h := h) ((1 / 2 : ℚ) ^ (i : ℕ)) (by positivity) (range i)
    rw [card_range] at this
    simp only [ha]; rw [aAnch_comp]; exact this
  have hB : ∀ j : Fin h, (b j).natDegree = j ∧ (b j).leadingCoeff = (1 / 2) ^ (j : ℕ) := fun j => by
    have := natDegree_lead_C_mul_PZ (h := h) ((1 / 2 : ℚ) ^ (j : ℕ)) (by positivity) (Ico (h + 1 - j) (h + 1))
    rw [Nat.card_Ico, show h + 1 - (h + 1 - j) = j by have := j.isLt; omega] at this
    simp only [hb]; rw [bAnch_comp h j (by have := j.isLt; omega)]; exact this
  have hM : (Matrix.of fun i j : Fin h => C (GA h i j) + X * C (GB h i j)) =
      (C ((2 : Q5) ^ (h + 2))) • Matrix.of (fun i j => LamQ h (a i * b j)) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, GA, GB, LamQ, ha, hb, mul_comp, C_mul]
    ring
  have hH : (HQ h).det = (Delta h).map (algebraMap ℚ Q5) := by
    rw [Delta_map hh]; rfl
  rw [hM, Matrix.det_smul, Fintype.card_fin,
    gram_eq a b (fun i => by rw [(hA i).1]; exact i.isLt) (fun j => by rw [(hB j).1]; exact j.isLt),
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_map_psiQ, det_map_psiQ,
    det_CoefM a (fun i => (hA i).1), det_CoefM b (fun j => (hB j).1), hH]
  simp only [fun i => (hA i).2, fun j => (hB j).2, psiQ_apply]
  have key : ((2 : Q5) ^ (h + 2)) ^ h * (((∏ i : Fin h, (1 / 2 : ℚ) ^ (i : ℕ)) : ℚ) : Q5) *
      (((∏ i : Fin h, (1 / 2 : ℚ) ^ (i : ℕ)) : ℚ) : Q5) = 2 ^ (3 * h) := by
    have := congrArg (fun r : ℚ => (r : Q5)) (scalar_eq h)
    push_cast at this ⊢
    rw [← this]; ring
  rw [← key]
  simp only [map_mul, map_pow]
  ring

/-! ### The entries -/

/-- **Lemma 10′ (L)**, `π = i + j − K ≥ 1`. -/
theorem lemma10_L {h i j : ℕ} (hh : Even h) (hi : i < h) (hj : j < h) (hπ : h + 2 ≤ i + j) :
    vGe 2 (-((i + j - (h + 1) : ℕ) : ℤ) - Nat.log 2 (i + j - (h + 1)) - 2) (GA h i j) ∧
      vGe 2 (-((i + j - (h + 1) : ℕ) : ℤ) - Nat.log 2 (i + j - (h + 1)) - 2) (GB h i j) := by
  refine ⟨?_, by rw [GB_L (by omega) (by omega) (by omega)]; exact vGe_zero _⟩
  rw [GA_L (by omega) (by omega) (by omega)]
  have hdeg : ((derivative (PZint h (Ico (h + 1 - j) i))).map (Int.castRingHom ℚ)).natDegree <
      i + j - (h + 1) := by
    rw [← derivative_map, ← PZ_eq_map]
    have hc : (PZ h (Ico (h + 1 - j) i)).natDegree = i + j - (h + 1) := by
      rw [natDegree_PZ, Nat.card_Ico]; omega
    rw [← hc]
    exact natDegree_derivative_lt (by rw [hc]; omega)
  refine vGe_mono ?_ (vGe_mul (vGe_of_V2 (V2_two_zpow _)) (vGe_Lmom_int _ hdeg))
  omega

/-- **Lemma 10′ (L)**, `π = 0`. -/
theorem lemma10_L0 {h i j : ℕ} (hh : Even h) (hij : i + j = h + 1) : GA h i j = 0 ∧ GB h i j = 0 := by
  refine ⟨?_, GB_L (by omega) (by omega) (by omega)⟩
  rw [GA_L (by omega) (by omega) (by omega), show Ico (h + 1 - j) i = ∅ by
    rw [Finset.Ico_eq_empty_iff]; omega]
  simp [PZint]

/-- **Lemma 10′ (U)**, `N₀ = K − 1 − i − j ≥ 1`. -/
theorem lemma10_U {h i j : ℕ} (hh : Even h) (hN : i + j < h) :
    vGe 2 (((h - i - j : ℕ) : ℤ) - Nat.log 2 (h - i - j)) (GA h i j) ∧
      vGe 2 (((h - i - j : ℕ) : ℤ) - Nat.log 2 (h - i - j)) (GB h i j) :=
  vGe_U hN.le

/-- **Lemma 10′ (U)**, `N₀ = 0`. -/
theorem lemma10_U0 {h i j : ℕ} (hh : Even h) (hij : i + j = h) : vGe 2 2 (GA h i j) ∧ vGe 2 2 (GB h i j) :=
  vGe_U0 hij

/-! ### The Leibniz bound -/

namespace TwoAdicAux

/-- Leibniz for polynomial matrices with row and column weights. -/
theorem vGeX_det2 {k : ℕ} (M : Matrix (Fin k) (Fin k) Q5[X]) (ρ κ : Fin k → ℤ)
    (h : ∀ i j, vGeX 2 (ρ i + κ j) (M i j)) : vGeX 2 (∑ i, ρ i + ∑ i, κ i) M.det := by
  rw [Matrix.det_apply]
  refine vGeX_sum _ _ (fun σ _ => ?_)
  have hprod : vGeX 2 (∑ i, (ρ (σ i) + κ i)) (∏ i, M (σ i) i) :=
    vGeX_prod _ _ _ (fun i _ => h (σ i) i)
  rw [sum_add_distrib, Equiv.sum_comp σ ρ] at hprod
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
  · simpa using hprod
  · simpa using vGeX_neg hprod

/-- The uniform entry bound `v₂(G_{ij}) ≥ K − i − j − ⌊log₂ h⌋ − 2`. -/
lemma vGe_entry {h i j : ℕ} (hh : Even h) (hi : i < h) (hj : j < h) :
    vGe 2 ((h : ℤ) - 1 - Nat.log 2 h - i - j) (GA h i j) ∧
      vGe 2 ((h : ℤ) - 1 - Nat.log 2 h - i - j) (GB h i j) := by
  rcases Nat.lt_or_ge (i + j) (h + 1) with hij | hij
  · have hU := vGe_U (h := h) (i := i) (j := j) (by omega)
    have hl := log_two_mono (show h - i - j ≤ h by omega)
    refine ⟨vGe_mono ?_ hU.1, vGe_mono ?_ hU.2⟩ <;> omega
  · rcases Nat.eq_or_lt_of_le hij with hij' | hij'
    · have := lemma10_L0 hh hij'.symm
      rw [this.1, this.2]; exact ⟨vGe_zero _, vGe_zero _⟩
    · have hL := lemma10_L hh hi hj (by omega)
      have hl := log_two_mono (show i + j - (h + 1) ≤ h by omega)
      refine ⟨vGe_mono ?_ hL.1, vGe_mono ?_ hL.2⟩ <;> omega

end TwoAdicAux

/-- **Lemma 10′**: `n₂ ≤ h⌊log₂ h⌋ + 3h`. -/
theorem padicNorm_Delta_two {h : ℕ} (hh : Even h) (k : ℕ) :
    padicNorm 2 ((Delta h).coeff k) ≤ (2 : ℚ) ^ e2 h := by
  set L := Nat.log 2 h with hL
  set ρ : Fin h → ℤ := fun i => (h : ℤ) - 1 - L - i with hρ
  set κ : Fin h → ℤ := fun j => -(j : ℤ) with hκ
  have hdet := vGeX_det2 (Matrix.of fun i j : Fin h => C (GA h i j) + X * C (GB h i j)) ρ κ (fun i j => by
    have := vGe_entry hh i.isLt j.isLt
    have e : ρ i + κ j = (h : ℤ) - 1 - L - i - j := by simp only [hρ, hκ]; ring
    rw [e, Matrix.of_apply]
    exact vGeX_add (vGeX_C this.1) (vGeX_X_mul (vGeX_C this.2)))
  have hsum : ∑ i, ρ i + ∑ i, κ i = -((h * L : ℕ) : ℤ) := by
    simp only [hρ, hκ, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, sum_neg_distrib]
    have h2 := Finset.sum_range_id_mul_two h
    rw [Fin.sum_univ_eq_sum_range (fun i => (i : ℤ)) h]
    have h3 : (∑ i ∈ range h, (i : ℤ)) * 2 = (h : ℤ) * ((h : ℤ) - 1) := by
      rcases h with _ | m
      · simp
      · have : (∑ i ∈ range (m + 1), (i : ℤ)) = ((∑ i ∈ range (m + 1), i : ℕ) : ℤ) := by push_cast; rfl
        rw [this]
        have h2' : ((∑ i ∈ range (m + 1), i : ℕ) : ℤ) * 2 = ((m + 1) * (m + 1 - 1) : ℕ) := by exact_mod_cast h2
        rw [h2']; push_cast; ring
    push_cast
    linear_combination (-1 : ℤ) * h3
  rw [hsum, det_anchored hh] at hdet
  have hinv : (Delta h).map (algebraMap ℚ Q5) =
      C ((((2 : ℚ) ^ (-((3 * h : ℕ) : ℤ))) : ℚ) : Q5) * (C ((2 : Q5) ^ (3 * h)) * (Delta h).map (algebraMap ℚ Q5)) := by
    rw [← mul_assoc, ← C_mul]
    have : ((((2 : ℚ) ^ (-((3 * h : ℕ) : ℤ))) : ℚ) : Q5) * (2 : Q5) ^ (3 * h) = 1 := by
      rw [zpow_neg, zpow_natCast, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat,
        inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)]
    rw [this, C_1, one_mul]
  have hfin := vGeX_mul (vGeX_C (vGe_of_V2 (V2_two_zpow (-((3 * h : ℕ) : ℤ))))) hdet
  rw [← hinv] at hfin
  have := padicNorm_coeff_of_vGeX_map hfin k
  refine this.trans (le_of_eq ?_)
  rw [show -(-((3 * h : ℕ) : ℤ) + -((h * L : ℕ) : ℤ)) = ((e2 h : ℕ) : ℤ) by unfold e2; push_cast; ring,
    zpow_natCast]
  norm_num

end Chi2U
