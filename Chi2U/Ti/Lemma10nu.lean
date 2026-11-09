/-
# Theorem V_i, Lemma 10_ν (PROOF_TI2 §2 row "§4 Lemma 10_ν" = PROOF_V §4 with `ν = v₂(n)`): `n₂(Δ_h) ≤ n2A n h`

**Copy of `Chi2U/V/Lemma10nu.lean`** for the Ti₂ machine at an even trace `n ≥ 4` (`ν = V.nuA n = v₂(n) ≥ 1`). Entries
`G_{ij}` of the rescaled anchored Gram matrix and their (L), (U) bounds: `Chi2U/Ti/TwoAdicNu.lean`. This file: the
Gram identity `det G = 2^{3h} Δ_h` at `zK n` (`det_anchoredM`, from `Ti.Delta_map`), the entry bound
`v₂(G_{ij}) ≥ ĝ(i + j)` (`vGe_entryM`), and the weighted Leibniz bound. The `z`-free parts (the concave minorant
`V.TwoAdicNu.gW`, its concavity, the closed form `V.TwoAdicNu.Sg` of `Σ_i ĝ(2i)`, and `V.three_h_sub_Sg_le`) are reused
from the χ₂ file: with `ν = v₂(n)` in place of `v₂(az)` the bounds are literally the same, so the bound is the χ₂
constant `V.n2A n h`.

**Departure from PROOF_V** (as in the χ₂ file): instead of majorisation/Karamata, the concavity of `ĝ` gives integer
row/column weights `⌊ĝ(2i)/2⌋`, `⌈ĝ(2j)/2⌉` with `ρ_i + κ_j ≤ ĝ(i + j)` and the weighted Leibniz bound
`v₂(det G) ≥ Σ_i ĝ(2i)`. Checked numerically: `scripts/ti/check_twoadic_ti.py` (n = 4, 6, 8, 10, 12, 16, 22, 32, 48,
h ≤ 16).
-/
import Chi2U.Ti.TwoAdicNu
import Chi2U.Ti.LemmaR
import Chi2U.V.Lemma10nu

set_option linter.unusedSectionVars false

namespace Chi2U.Ti.TwoAdicNu

open Polynomial Finset Chi2U.TwoAdicAux

variable {n : ℕ} [Fact (3 ≤ n)]

/-! ### The Gram identity at `zK n` -/

/-- `Λ_X(g) = A(g) + X·B(g) ∈ ℚ(√d)[X]`. -/
noncomputable def LamQM (n : ℕ) [Fact (3 ≤ n)] (h : ℕ) (g : ℚ[X]) : (Qt n)[X] :=
  C (Afun n h g) + X * C (Bfun n h g)

lemma LamQM_add (h : ℕ) (f g : ℚ[X]) : LamQM n h (f + g) = LamQM n h f + LamQM n h g := by
  unfold LamQM; rw [Afun_addM, Bfun_addM, C_add, C_add]; ring

lemma LamQM_C_mul (h : ℕ) (c : ℚ) (g : ℚ[X]) : LamQM n h (C c * g) = C (c : Qt n) * LamQM n h g := by
  unfold LamQM; rw [Afun_C_mulM, Bfun_C_mulM, C_mul, C_mul]; ring

lemma LamQM_sum (h : ℕ) {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    LamQM n h (∑ i ∈ s, f i) = ∑ i ∈ s, LamQM n h (f i) :=
  map_sum (AddMonoidHom.mk' (LamQM n h) (LamQM_add h)) f s

/-- `ℚ → ℚ(√d)[X]`. -/
noncomputable def psiQd (n : ℕ) [Fact (3 ≤ n)] : ℚ →+* (Qt n)[X] := C.comp (algebraMap ℚ (Qt n))

lemma psiQd_apply (r : ℚ) : psiQd n r = C (r : Qt n) := by simp [psiQd]

/-- The monomial matrix `H_{de} = Λ_X(t^{d+e})`. -/
noncomputable def HQM (n : ℕ) [Fact (3 ≤ n)] (h : ℕ) : Matrix (Fin h) (Fin h) (Qt n)[X] :=
  fun d e => LamQM n h (X ^ ((d : ℕ) + e))

theorem gram_eqM {h : ℕ} (a b : Fin h → ℚ[X]) (ha : ∀ i, (a i).natDegree < h) (hb : ∀ i, (b i).natDegree < h) :
    Matrix.of (fun i j => LamQM n h (a i * b j)) =
      (CoefM a).map (psiQd n) * HQM n h * ((CoefM b).map (psiQd n)).transpose := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [expand_fin a ha i, expand_fin b hb j, sum_mul_sum, LamQM_sum]
  simp only [LamQM_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun e _ => ?_)
  rw [sum_mul]
  refine sum_congr rfl (fun d _ => ?_)
  have : C (CoefM a i d) * X ^ (d : ℕ) * (C (CoefM b j e) * X ^ (e : ℕ)) =
      C (CoefM a i d * CoefM b j e) * X ^ ((d : ℕ) + e) := by
    rw [C_mul, pow_add]; ring
  rw [this, LamQM_C_mul, psiQd_apply, psiQd_apply, Rat.cast_mul, C_mul]
  simp only [HQM]
  ring

lemma det_map_psiQd {h : ℕ} (M : Matrix (Fin h) (Fin h) ℚ) : (M.map (psiQd n)).det = psiQd n M.det :=
  (RingHom.map_det (psiQd n) M).symm

/-- Rescaling and the unitriangular change of basis at `zK n`: `det G = 2^{3h} Δ_h`. -/
theorem det_anchoredM {h : ℕ} (hh : Even h) :
    (Matrix.of fun i j : Fin h => C (GAm n h i j) + X * C (GBm n h i j)).det =
      C ((2 : Qt n) ^ (3 * h)) * (Delta n h).map (algebraMap ℚ (Qt n)) := by
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
  have hM : (Matrix.of fun i j : Fin h => C (GAm n h i j) + X * C (GBm n h i j)) =
      (C ((2 : Qt n) ^ (h + 2))) • Matrix.of (fun i j => LamQM n h (a i * b j)) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, GAm, GBm, LamQM, ha, hb, mul_comp, C_mul]
    ring
  have hH : (HQM n h).det = (Delta n h).map (algebraMap ℚ (Qt n)) := by
    rw [Ti.Delta_map hh]; rfl
  rw [hM, Matrix.det_smul, Fintype.card_fin,
    gram_eqM a b (fun i => by rw [(hA i).1]; exact i.isLt) (fun j => by rw [(hB j).1]; exact j.isLt),
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_map_psiQd, det_map_psiQd,
    det_CoefM a (fun i => (hA i).1), det_CoefM b (fun j => (hB j).1), hH]
  simp only [fun i => (hA i).2, fun j => (hB j).2, psiQd_apply]
  have key : ((2 : Qt n) ^ (h + 2)) ^ h * (((∏ i : Fin h, (1 / 2 : ℚ) ^ (i : ℕ)) : ℚ) : Qt n) *
      (((∏ i : Fin h, (1 / 2 : ℚ) ^ (i : ℕ)) : ℚ) : Qt n) = 2 ^ (3 * h) := by
    have := congrArg (fun r : ℚ => (r : Qt n)) (scalar_eq h)
    push_cast at this ⊢
    rw [← this]; ring
  rw [← key]
  simp only [map_mul, map_pow]
  ring

/-! ### The concave entry bound -/

/-- **Entry bound** (PROOF_V (L), (U), coarsened, `ν = v₂(n)`): `v₂(G_{ij}) ≥ ĝ(i + j)`, `ĝ = V.TwoAdicNu.gW n h`. -/
theorem vGe_entryM (ha : Even n) {h i j : ℕ} (hi : i < h) (hj : j < h) :
    vGe 2 (V.TwoAdicNu.gW n h ((i : ℤ) + j)) (GAm n h i j) ∧
      vGe 2 (V.TwoAdicNu.gW n h ((i : ℤ) + j)) (GBm n h i j) := by
  unfold V.TwoAdicNu.gW
  split_ifs with hν
  · rcases Nat.lt_or_ge (i + j) (h + 1) with hij | hij
    · have hU := vGe_UM (n := n) (h := h) (i := i) (j := j) hν (by omega)
      have hl := log_two_mono (show h - i - j ≤ h by omega)
      have hle : min ((h : ℤ) - (i + j) - Nat.log 2 h - 2)
          (-3 - ((V.nuA n : ℤ) - 1) * ((i : ℤ) + j - (h + 1)) - Nat.log 2 h) ≤
          ((h - i - j : ℕ) : ℤ) - Nat.log 2 (h - i - j) := by
        refine (min_le_left _ _).trans ?_
        omega
      exact ⟨vGe_mono hle hU.1, vGe_mono hle hU.2⟩
    · rcases Nat.eq_or_lt_of_le hij with hij' | hij'
      · have := lemma10_L0M (n := n) hij'.symm
        rw [this.1, this.2]; exact ⟨vGe_zero _, vGe_zero _⟩
      · have hL := lemma10_LM (n := n) hν hi hj (by omega)
        have hl := log_two_mono (show i + j - (h + 1) ≤ h by omega)
        have hle : min ((h : ℤ) - (i + j) - Nat.log 2 h - 2)
            (-3 - ((V.nuA n : ℤ) - 1) * ((i : ℤ) + j - (h + 1)) - Nat.log 2 h) ≤
            -((V.nuA n : ℤ) - 1) * ((i + j - (h + 1) : ℕ) : ℤ) - 2 - Nat.log 2 (i + j - (h + 1)) := by
          refine (min_le_right _ _).trans ?_
          push_cast [show h + 1 ≤ i + j by omega]
          have : ((Nat.log 2 (i + j - (h + 1)) : ℕ) : ℤ) ≤ Nat.log 2 h := by exact_mod_cast hl
          nlinarith
        refine ⟨vGe_mono hle hL.1, ?_⟩
        rw [hL.2]; exact vGe_zero _
  · have hν1 : V.nuA n = 1 := by have := one_le_nuA ha; omega
    rcases Nat.lt_or_ge (i + j) (h + 1) with hij | hij
    · have hU := vGe_UM1 (n := n) ha (h := h) (i := i) (j := j) (by omega)
      have hle : min (0 : ℤ) ((h : ℤ) + 1 - (i + j)) ≤ 1 := (min_le_left _ _).trans (by norm_num)
      exact ⟨vGe_mono hle hU.1, vGe_mono hle hU.2⟩
    · rcases Nat.eq_or_lt_of_le hij with hij' | hij'
      · have := lemma10_L0M (n := n) hij'.symm
        rw [this.1, this.2]; exact ⟨vGe_zero _, vGe_zero _⟩
      · have hL := lemma10_LM1 (n := n) hν1 hi hj (by omega)
        have hle : min (0 : ℤ) ((h : ℤ) + 1 - (i + j)) ≤ -((i + j - (h + 1) : ℕ) : ℤ) := by
          refine (min_le_right _ _).trans ?_
          push_cast [show h + 1 ≤ i + j by omega]
          omega
        refine ⟨vGe_mono hle hL.1, ?_⟩
        rw [hL.2]; exact vGe_zero _

/-! ### Leibniz with row and column weights -/

/-- Leibniz for polynomial matrices with row and column weights. -/
theorem vGeX_det2M {k : ℕ} (M : Matrix (Fin k) (Fin k) (Qt n)[X]) (ρ κ : Fin k → ℤ)
    (h : ∀ i j, vGeX 2 (ρ i + κ j) (M i j)) : vGeX 2 (∑ i, ρ i + ∑ i, κ i) M.det := by
  rw [Matrix.det_apply]
  refine vGeX_sum _ _ (fun σ _ => ?_)
  have hprod : vGeX 2 (∑ i, (ρ (σ i) + κ i)) (∏ i, M (σ i) i) :=
    vGeX_prod _ _ _ (fun i _ => h (σ i) i)
  rw [sum_add_distrib, Equiv.sum_comp σ ρ] at hprod
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
  · simpa using hprod
  · simpa using vGeX_neg hprod

/-- `v₂(det G) ≥ Σ_i ĝ(2i)` (the weights `⌊ĝ(2i)/2⌋`, `⌈ĝ(2j)/2⌉`). -/
theorem vGeX_detG (ha : Even n) {h : ℕ} (hh : Even h) (h2 : 2 ≤ h) :
    vGeX 2 (V.TwoAdicNu.Sg n h) (Matrix.of fun i j : Fin h => C (GAm n h i j) + X * C (GBm n h i j)).det := by
  set ρ : Fin h → ℤ := fun i => V.TwoAdicNu.gW n h (2 * ((i : ℕ) : ℤ)) / 2 with hρ
  set κ : Fin h → ℤ := fun j => V.TwoAdicNu.gW n h (2 * ((j : ℕ) : ℤ)) -
    V.TwoAdicNu.gW n h (2 * ((j : ℕ) : ℤ)) / 2 with hκ
  have hdet := vGeX_det2M (Matrix.of fun i j : Fin h => C (GAm n h i j) + X * C (GBm n h i j)) ρ κ
    (fun i j => by
      have hE := vGe_entryM (n := n) ha (h := h) i.isLt j.isLt
      have hc := V.TwoAdicNu.gW_concave n h ((i : ℕ) : ℤ) ((j : ℕ) : ℤ)
      have hle : ρ i + κ j ≤ V.TwoAdicNu.gW n h (((i : ℕ) : ℤ) + ((j : ℕ) : ℤ)) := by
        simp only [hρ, hκ]; omega
      rw [Matrix.of_apply]
      exact vGeX_add (vGeX_C (vGe_mono hle hE.1)) (vGeX_X_mul (vGeX_C (vGe_mono hle hE.2))))
  have hsum : ∑ i, ρ i + ∑ i, κ i = V.TwoAdicNu.Sg n h := by
    rw [← sum_add_distrib, ← V.TwoAdicNu.sum_gW n hh h2,
      ← Fin.sum_univ_eq_sum_range (fun i => V.TwoAdicNu.gW n h (2 * (i : ℤ))) h]
    refine sum_congr rfl (fun i _ => ?_)
    simp only [hρ, hκ]; ring
  rwa [hsum] at hdet

end Chi2U.Ti.TwoAdicNu

namespace Chi2U.Ti

open Polynomial Finset Chi2U.TwoAdicAux Chi2U.Ti.TwoAdicNu

/-- **Lemma 10_ν** (PROOF_TI2 §2 = PROOF_V §4 with `ν = v₂(n)`): `n₂(Δ_h) ≤ n2A n h` for even `h ≥ 2` at every even
trace `n ≥ 4`. Route (as `Chi2U.V.lemma10nu_proof`): `Δ_h = 2^{−3h} det G` (`det_anchoredM`) and
`v₂(det G) ≥ Σ_i ĝ(2i)` (`vGeX_detG`, entry bounds `vGe_entryM`). -/
theorem lemma10nu_proof (n : ℕ) [Fact (3 ≤ n)] (hn : Even n) {h : ℕ} (hh : Even h) (h2 : 2 ≤ h) (k : ℕ) :
    padicNorm 2 ((Delta n h).coeff k) ≤ (2 : ℚ) ^ V.n2A n h := by
  have hdet := vGeX_detG (n := n) hn hh h2
  rw [det_anchoredM hh] at hdet
  have hinv : (Delta n h).map (algebraMap ℚ (Qt n)) =
      C ((((2 : ℚ) ^ (-((3 * h : ℕ) : ℤ))) : ℚ) : Qt n) *
        (C ((2 : Qt n) ^ (3 * h)) * (Delta n h).map (algebraMap ℚ (Qt n))) := by
    rw [← mul_assoc, ← C_mul]
    have : ((((2 : ℚ) ^ (-((3 * h : ℕ) : ℤ))) : ℚ) : Qt n) * (2 : Qt n) ^ (3 * h) = 1 := by
      rw [zpow_neg, zpow_natCast, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat,
        inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)]
    rw [this, C_1, one_mul]
  have hfin := vGeX_mul (vGeX_C (vGe_of_V2M (n := n) (V2_two_zpow (-((3 * h : ℕ) : ℤ))))) hdet
  rw [← hinv] at hfin
  refine (padicNorm_coeff_of_vGeX_map hfin k).trans ?_
  rw [← zpow_natCast]
  refine zpow_le_zpow_right₀ (by norm_num) ?_
  have := V.three_h_sub_Sg_le n hh h2
  push_cast at this ⊢
  linarith

end Chi2U.Ti
