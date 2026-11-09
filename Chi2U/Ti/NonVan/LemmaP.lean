/-
# Theorem V_i: Lemma P′_n, nonvanishing along `h = 3ℓ − 1` (PROOF_TI2 §4, PROOF_V §6, PROOF_U §6)

**Copy of `Chi2U/NonVan/LemmaP.lean`** with the sign fixed (namespace `Chi2U.Ti.LP`). Reused from the χ₂ files (they do
not see `z`): `decomp_lt`, `sig3`, `tl`, `padicNorm_tl`, `padicValRat_tl`, `padicNorm_pow'`, `padicValRat_prod_dPrime`,
`dv`, `Mblk`, `sum_adjugate_blockB`, `padicValRat_dPrime`.

`ℓ ≥ 7` prime with `ℓ ∤ n`, `h = 3ℓ − 1`, `K = 3ℓ`. Congruences are taken in the residue field `Fl n ℓ = O_ℓ/𝔩` for a
maximal ideal `𝔩 ∋ ℓ` of `O_ℓ ⊂ K = ℚ(√d)` (`Ti/NonVan/ModL.lean`), with `y = −z²` and `ζ := z^ℓ` itself: no Frobenius
identification of `ζ` (PROOF_TI2's four classes `w^ℓ ≡ ζ`) is needed, only `1 − ȳ^ℓ = (n·z̄)^ℓ`. Steps (PROOF_U §6):
1. Lemma B (`Ti/NonVan/LemmaB.lean`): `Δ_h(X)·Π D′(x_i) = ± 𝟙ᵀ adj(G^f(X)) 𝟙`;
2. `B(f_i f_j) = 0` (`i ≠ j`), `B(f_i²) = −D′(x_i) sgn(x_i) z^{x_i}` (`Bfun_fLag_offdiag`, `Bfun_fLag_diag`);
3. `G^f(0)` is `ℓ`-integral and block diagonal mod `𝔩` over the classes (`blockDiag`);
4. its class blocks are `≡ e_γ (c𝟙𝟙ᵀ + diag(8εζ, 0, 8εζ³))`, `e_γ = −(−1)^γ τ z^{x_γ}`, `c = τ ζ³/(n·z)^ℓ`,
   `τ = (−1)^{(3ℓ−1)/2}`, `ε = (−1)^{(ℓ−1)/2}` (`blockClosed`, from `Cong_Afun`, `Ti/NonVan/Gram0.lean`);
5. the bordered determinant of the block-diagonal reduction is a unit (`Ti/NonVan/BlockDet.lean`), so
   `v_ℓ(c₀) = −2K` (`lemmaP_coeff_zero`);
6. `[X^k]` gains `2k` (`lemmaP_coeff_le`); hence `Δ_h(a/b) ≠ 0` when `ℓ² ∤ b` (`lemmaP`).
`nonvan_frequently` packages this for the endgame (`MachineBoundsT.nonvan`).

The intermediate steps assume `ℓ ∤ 2n` (`hℓm`), which makes `2`, `z`, `n` (hence `1 − y = n·z`) units mod `𝔩`; `𝔩`
is any maximal ideal over `ℓ` (ramified `ℓ ∣ n² − 4` included), so `ℓ ∤ n² − 4` is not used.
-/
import Chi2U.Ti.NonVan.BlockDet
import Chi2U.NonVan.LemmaP

namespace Chi2U
namespace Ti
namespace LP

open Polynomial Finset Filter
open Chi2U.LP (sig3 tl padicNorm_tl padicValRat_tl padicNorm_pow' padicValRat_prod_dPrime dv Mblk
  sum_adjugate_blockB padicValRat_dPrime)

variable {n : ℕ} [Fact (3 ≤ n)] {ℓ : ℕ}

/-- Step 2, off-diagonal: `B(f_i f_j) = 0` for `i ≠ j` (`f_i f_j / D` is a polynomial). -/
theorem Bfun_fLag_offdiag {h i j : ℕ} (hh : Even h) (hi : i ≤ h) (hj : j ≤ h) (hij : i ≠ j) :
    Bfun n h (fLag h i * fLag h j) = 0 := by
  rw [Bfun_ff j hi, if_neg hij]

/-- Step 2, diagonal: `B(f_i²) = −D′(x_i) sgn(x_i) z^{x_i}`. -/
theorem Bfun_fLag_diag {h i : ℕ} (hh : Even h) (hi : i ≤ h) :
    Bfun n h (fLag h i * fLag h i) =
      -((dPrime h i : ℚ) : Qt n) * (sgnPole (poleZ h i) : Qt n) * (zK n) ^ (poleZ h i) := by
  rw [Bfun_ff i hi, if_pos rfl]; ring

/-- Step 3: `G^f(0)` is `ℓ`-integral and vanishes mod `𝔩` between different classes. -/
theorem blockDiag [Fact ℓ.Prime] (hℓ : 7 ≤ ℓ) (hℓm : ¬ ℓ ∣ 2 * n) {i j : ℕ} (hi : i < 3 * ℓ) (hj : j < 3 * ℓ) :
    vGe ℓ 0 (Afun n (3 * ℓ - 1) (fLag (3 * ℓ - 1) i * fLag (3 * ℓ - 1) j)) ∧
      (i % ℓ ≠ j % ℓ → Cong ℓ (Afun n (3 * ℓ - 1) (fLag (3 * ℓ - 1) i * fLag (3 * ℓ - 1) j)) 0) := by
  have hℓ2 : ℓ ≠ 2 := by omega
  obtain ⟨hγ, hr, hi'⟩ := decomp_lt (by omega) hi
  obtain ⟨hγ', hs, hj'⟩ := decomp_lt (by omega) hj
  have h := Cong_Afun hℓm hγ hγ' hr hs
  rw [hi', hj'] at h
  refine ⟨vGe_of_pInt h.mem, fun hne => ?_⟩
  rwa [if_neg hne] at h

/-- Step 4: the class blocks in closed form, `G^f(0)_{γ+rℓ, γ+sℓ} ≡ e_γ (c + [r = s] d_r)` mod `𝔩`. -/
theorem blockClosed [Fact ℓ.Prime] (hℓ : 7 ≤ ℓ) (hℓm : ¬ ℓ ∣ 2 * n) {γ r s : ℕ} (hγ : γ < ℓ) (hr : r < 3) (hs : s < 3) :
    Cong ℓ (Afun n (3 * ℓ - 1) (fLag (3 * ℓ - 1) (γ + r * ℓ) * fLag (3 * ℓ - 1) (γ + s * ℓ)))
      (eB n ℓ γ * (cB n ℓ + if r = s then dB n ℓ r else 0)) := by
  have h := Cong_Afun hℓm hγ hγ hr hs
  rwa [if_pos rfl] at h


section S
variable [hℓ : Fact ℓ.Prime]

variable (n ℓ) in
/-- The block-diagonal model of `G^f(0)` mod `𝔩`. -/
noncomputable def Bmat : Matrix (Fin 3 × Fin ℓ) (Fin 3 × Fin ℓ) (Fl n ℓ) :=
  Matrix.blockDiagonal (Mblk (fun γ : Fin ℓ => eB n ℓ γ) (cB n ℓ) (8 * (-1) ^ (ℓ / 2) * zb n ℓ ^ ℓ)
    (8 * (-1) ^ (ℓ / 2) * zb n ℓ ^ (3 * ℓ)))

lemma dv_eq_dB (r : Fin 3) :
    dv (8 * (-1) ^ (ℓ / 2) * zb n ℓ ^ ℓ) (8 * (-1) ^ (ℓ / 2) * zb n ℓ ^ (3 * ℓ)) r = dB n ℓ r := by
  fin_cases r <;> simp [dv, dB]

lemma Cong_G0 (hℓm : ¬ ℓ ∣ 2 * n) (a b : Fin (3 * ℓ - 1 + 1)) :
    Cong ℓ (Afun n (3 * ℓ - 1) (fLag (3 * ℓ - 1) a * fLag (3 * ℓ - 1) b)) (Bmat n ℓ (sig3 ℓ a) (sig3 ℓ b)) := by
  have hl := hℓ.out.pos
  have ha : (a : ℕ) < 3 * ℓ := by have := a.isLt; omega
  have hb : (b : ℕ) < 3 * ℓ := by have := b.isLt; omega
  obtain ⟨hγ, hr, ha'⟩ := decomp_lt hl ha
  obtain ⟨hγ', hs, hb'⟩ := decomp_lt hl hb
  have h := Cong_Afun hℓm hγ hγ' hr hs
  rw [ha', hb'] at h
  refine Cong_congr h rfl ?_
  simp only [Bmat, sig3, Equiv.coe_fn_mk, Matrix.blockDiagonal_apply, Mblk, Matrix.of_apply]
  by_cases hg : (a : ℕ) % ℓ = (b : ℕ) % ℓ
  · have hg' : (⟨(a : ℕ) % ℓ, hγ⟩ : Fin ℓ) = ⟨(b : ℕ) % ℓ, hγ'⟩ := Fin.ext hg
    rw [if_pos hg, if_pos hg']
    by_cases hrs : (a : ℕ) / ℓ = (b : ℕ) / ℓ
    · have hrs' : (⟨(a : ℕ) / ℓ, hr⟩ : Fin 3) = ⟨(b : ℕ) / ℓ, hs⟩ := Fin.ext hrs
      rw [if_pos hrs, if_pos hrs', dv_eq_dB]
    · have hrs' : (⟨(a : ℕ) / ℓ, hr⟩ : Fin 3) ≠ ⟨(b : ℕ) / ℓ, hs⟩ := fun e => hrs (Fin.ext_iff.mp e)
      rw [if_neg hrs, if_neg hrs']
  · have hg' : (⟨(a : ℕ) % ℓ, hγ⟩ : Fin ℓ) ≠ ⟨(b : ℕ) % ℓ, hγ'⟩ := fun e => hg (Fin.ext_iff.mp e)
    rw [if_neg hg, if_neg hg']

lemma eB_ne_zero (γ : ℕ) : eB n ℓ γ ≠ 0 :=
  mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) tauB_ne_zero))
    (zpow_ne_zero _ zb_ne_zero)

lemma cB_ne_zero (hℓm : ¬ ℓ ∣ 2 * n) : cB n ℓ ≠ 0 :=
  mul_ne_zero (mul_ne_zero tauB_ne_zero
    (inv_ne_zero (pow_ne_zero _ (mul_ne_zero (n_ne_zero_Fl hℓm) zb_ne_zero))))
    (pow_ne_zero _ zb_ne_zero)

lemma eps_ne_zero : ((-1 : Fl n ℓ) ^ (ℓ / 2)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)

lemma eight_ne_zero_Fl (hℓ2 : ℓ ≠ 2) : (8 : Fl n ℓ) ≠ 0 := by
  rw [show (8 : Fl n ℓ) = 4 * 2 by norm_num]; exact mul_ne_zero (four_ne_zero_Fl hℓ2) (two_ne_zero_Fl hℓ2)

/-- Step 5: the bordered determinant of the reduction is nonzero. -/
lemma sum_adj_Bmat_ne_zero (hℓm : ¬ ℓ ∣ 2 * n) : ∑ p, ∑ q, (Bmat n ℓ).adjugate p q ≠ 0 := by
  rw [Bmat, sum_adjugate_blockB _ _ _ _ (fun γ : Fin ℓ => eB_ne_zero (γ : ℕ)) (cB_ne_zero hℓm)]
  have hℓ2 : ℓ ≠ 2 := ne_two_of_not_dvd hℓm
  have hz := zb_ne_zero (n := n) (ℓ := ℓ)
  refine mul_ne_zero (prod_ne_zero_iff.mpr (fun γ _ => mul_ne_zero (pow_ne_zero _ (eB_ne_zero γ))
    (mul_ne_zero (mul_ne_zero (cB_ne_zero hℓm)
        (mul_ne_zero (mul_ne_zero (eight_ne_zero_Fl hℓ2) eps_ne_zero) (pow_ne_zero _ hz)))
      (mul_ne_zero (mul_ne_zero (eight_ne_zero_Fl hℓ2) eps_ne_zero) (pow_ne_zero _ hz)))))
    (mul_ne_zero (inv_ne_zero (cB_ne_zero hℓm)) ?_)
  rw [Fin.sum_univ_eq_sum_range (fun γ => (eB n ℓ γ)⁻¹)]
  exact sum_inv_eB_ne_zero hℓm

/-- `G^f(0)` as a matrix over `O_ℓ`. -/
noncomputable def G0R (hℓm : ¬ ℓ ∣ 2 * n) : Matrix (Fin (3 * ℓ - 1 + 1)) (Fin (3 * ℓ - 1 + 1)) (Rl n ℓ) :=
  fun a b => ⟨Afun n (3 * ℓ - 1) (fLag (3 * ℓ - 1) a * fLag (3 * ℓ - 1) b), (Cong_G0 hℓm a b).mem⟩

lemma red_sum_adj_G0R (hℓm : ¬ ℓ ∣ 2 * n) : red n ℓ (∑ a, ∑ b, (G0R hℓm).adjugate a b) ≠ 0 := by
  have hmap : (red n ℓ).mapMatrix (G0R hℓm) = (Bmat n ℓ).submatrix (sig3 ℓ) (sig3 ℓ) := by
    ext a b
    exact (Cong_red (G0R hℓm a b)).unique (Cong_G0 hℓm a b)
  simp only [map_sum]
  have e : ∀ a b, red n ℓ ((G0R hℓm).adjugate a b) = ((red n ℓ).mapMatrix (G0R hℓm)).adjugate a b := by
    intro a b
    rw [← RingHom.map_adjugate]; rfl
  simp only [e, hmap, Matrix.adjugate_submatrix_equiv_self, Matrix.submatrix_apply]
  have hre : ∑ a, ∑ b, (Bmat n ℓ).adjugate (sig3 ℓ a) (sig3 ℓ b) = ∑ p, ∑ q, (Bmat n ℓ).adjugate p q := by
    rw [← Equiv.sum_comp (sig3 ℓ) (fun p => ∑ q, (Bmat n ℓ).adjugate p q)]
    exact sum_congr rfl (fun a _ => Equiv.sum_comp (sig3 ℓ) (fun q => (Bmat n ℓ).adjugate (sig3 ℓ a) q))
  rw [hre]; exact sum_adj_Bmat_ne_zero hℓm

omit hℓ in
/-- Lemma B at `X = 0`. -/
lemma lemmaB_zero (hh : Even (3 * ℓ - 1)) :
    (((Delta n (3 * ℓ - 1)).coeff 0 : ℚ) : Qt n) * ∏ i ∈ range (3 * ℓ - 1 + 1), ((dPrime (3 * ℓ - 1) i : ℚ) : Qt n) =
      (-1) ^ ((3 * ℓ - 1 + 1) * (3 * ℓ - 1) / 2) *
        ∑ a, ∑ b, (Matrix.of fun a b : Fin (3 * ℓ - 1 + 1) =>
          Afun n (3 * ℓ - 1) (fLag (3 * ℓ - 1) a * fLag (3 * ℓ - 1) b)).adjugate a b := by
  have h := congrArg (Polynomial.evalRingHom (0 : Qt n)) (lemmaB hh)
  simp only [map_mul, map_sum, coe_evalRingHom, eval_C] at h
  rw [eval_map, eval₂_at_zero, eq_ratCast] at h
  rw [h]
  congr 1
  have hG : (evalRingHom (0 : Qt n)).mapMatrix (GramF n (3 * ℓ - 1)) = Matrix.of fun a b : Fin (3 * ℓ - 1 + 1) =>
      Afun n (3 * ℓ - 1) (fLag (3 * ℓ - 1) a * fLag (3 * ℓ - 1) b) := by
    refine Matrix.ext fun a b => ?_
    simp [GramF, LamX]
  rw [← hG]
  refine sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => ?_))
  rw [← RingHom.map_adjugate]; rfl

end S

/-- Step 5: `v_ℓ(c₀) = −2K`. -/
theorem lemmaP_coeff_zero [Fact ℓ.Prime] (hℓ : 7 ≤ ℓ) (hℓm : ¬ ℓ ∣ 2 * n) :
    padicValRat ℓ ((Delta n (3 * ℓ - 1)).coeff 0) = -(2 * (3 * ℓ) : ℤ) ∧ (Delta n (3 * ℓ - 1)).coeff 0 ≠ 0 := by
  have hℓ2 : ℓ ≠ 2 := by omega
  have hh : Even (3 * ℓ - 1) := by
    obtain ⟨k, hk⟩ := (Fact.out : ℓ.Prime).odd_of_ne_two hℓ2
    exact ⟨3 * k + 1, by omega⟩
  set c0 := (Delta n (3 * ℓ - 1)).coeff 0
  set P := ∏ i ∈ range (3 * ℓ - 1 + 1), dPrime (3 * ℓ - 1) i with hP
  have hP0 : P ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => LB.dPrime_ne_zero _ _)
  have hB := lemmaB_zero (n := n) hh
  set s : Qt n := (-1) ^ ((3 * ℓ - 1 + 1) * (3 * ℓ - 1) / 2)
  -- the bordered determinant `w` reduces to a nonzero element
  have hG : (Matrix.of fun a b : Fin (3 * ℓ - 1 + 1) =>
      Afun n (3 * ℓ - 1) (fLag (3 * ℓ - 1) a * fLag (3 * ℓ - 1) b)) = (Rl n ℓ).subtype.mapMatrix (G0R hℓm) := by
    exact Matrix.ext fun a b => rfl
  have hw : ∑ a, ∑ b, (Matrix.of fun a b : Fin (3 * ℓ - 1 + 1) =>
      Afun n (3 * ℓ - 1) (fLag (3 * ℓ - 1) a * fLag (3 * ℓ - 1) b)).adjugate a b =
      (((∑ a, ∑ b, (G0R hℓm).adjugate a b : Rl n ℓ)) : Qt n) := by
    rw [hG]
    have e : ∀ a b, ((Rl n ℓ).subtype.mapMatrix (G0R hℓm)).adjugate a b =
        (Rl n ℓ).subtype ((G0R hℓm).adjugate a b) := by
      intro a b; rw [← RingHom.map_adjugate]; rfl
    simp only [e, ← map_sum]; rfl
  have hCw := Cong_red (∑ a, ∑ b, (G0R hℓm).adjugate a b)
  rw [← hw] at hCw
  have hs : Cong ℓ s ((-1) ^ ((3 * ℓ - 1 + 1) * (3 * ℓ - 1) / 2)) :=
    Cong_pow (Cong_neg Cong_one) _
  have hq : Cong ℓ (((c0 * P : ℚ)) : Qt n)
      ((-1) ^ ((3 * ℓ - 1 + 1) * (3 * ℓ - 1) / 2) * red n ℓ (∑ a, ∑ b, (G0R hℓm).adjugate a b)) := by
    have e : (((c0 * P : ℚ)) : Qt n) = c0 * ∏ i ∈ range (3 * ℓ - 1 + 1), ((dPrime (3 * ℓ - 1) i : ℚ) : Qt n) := by
      rw [hP]; push_cast; rfl
    rw [e, hB]
    exact Cong_mul hs hCw
  have hne : ((-1 : Fl n ℓ) ^ ((3 * ℓ - 1 + 1) * (3 * ℓ - 1) / 2) *
      red n ℓ (∑ a, ∑ b, (G0R hℓm).adjugate a b)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (red_sum_adj_G0R hℓm)
  have h1 := padicNorm_eq_one_of_Cong hq hne
  have hq0 : c0 * P ≠ 0 := by intro h0; rw [h0, padicNorm.zero] at h1; exact zero_ne_one h1
  have hc0 : c0 ≠ 0 := left_ne_zero_of_mul hq0
  have hv : padicValRat ℓ (c0 * P) = 0 := by
    rw [padicNorm.eq_zpow_of_nonzero hq0] at h1
    have hl : (1 : ℚ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
    have := (zpow_right_injective₀ (by linarith : (0 : ℚ) < ℓ) hl.ne') (h1.trans (zpow_zero _).symm)
    omega
  rw [padicValRat.mul hc0 hP0, padicValRat_prod_dPrime hℓ2] at hv
  exact ⟨by omega, hc0⟩

/-! ### Step 6 -/


section S
variable [hℓ : Fact ℓ.Prime]

variable (n ℓ) in
/-- Polynomials over `ℚ(√d)` with `ℓ`-integral coefficients. -/
def RX : Subring (Qt n)[X] where
  carrier := {P | vGeX ℓ 0 P}
  mul_mem' ha hb := by simpa using vGeX_mul ha hb
  one_mem' := vGeX_one
  add_mem' := vGeX_add
  zero_mem' := fun k => by rw [coeff_zero]; exact vGe_zero 0
  neg_mem' := vGeX_neg

/-- The substituted Gram entries `Λ_{X/ℓ²}(f_i f_j)` have `ℓ`-integral coefficients. -/
lemma GramF_comp_mem (hℓm : ¬ ℓ ∣ 2 * n) (a b : Fin (3 * ℓ - 1 + 1)) :
    (GramF n (3 * ℓ - 1) a b).comp (C ((tl ℓ : ℚ) : Qt n) * X) ∈ RX n ℓ := by
  have hℓ2 : ℓ ≠ 2 := ne_two_of_not_dvd hℓm
  have hA := (Cong_G0 hℓm a b).mem
  have hl := hℓ.out.pos
  have ha : (a : ℕ) ≤ 3 * ℓ - 1 := Nat.lt_succ_iff.mp a.isLt
  have hB : vGe ℓ 0 (((tl ℓ : ℚ) : Qt n) * Bfun n (3 * ℓ - 1) (fLag (3 * ℓ - 1) a * fLag (3 * ℓ - 1) b)) := by
    rw [Bfun_ff _ ha]
    split_ifs with hab
    · obtain ⟨hγ, hr, ha'⟩ := decomp_lt hl (show (a : ℕ) < 3 * ℓ by omega)
      have hv := padicValRat_dPrime hℓ2 hγ hr
      rw [ha'] at hv
      have h1 := vGe_ratCast (n := n) (p := ℓ) (dPrime (3 * ℓ - 1) a)
      rw [hv] at h1
      have h2 := vGe_ratCast (n := n) (p := ℓ) (tl ℓ)
      rw [padicValRat_tl] at h2
      have hsg : pInt ℓ ((sgnPole (poleZ (3 * ℓ - 1) a) : ℚ) : Qt n) := by
        unfold sgnPole; push_cast; exact pInt_pow (pInt_neg pInt_one) _
      have h3 := vGe_mul (vGe_mul (vGe_mul h2 h1) (vGe_of_pInt hsg)) (vGe_zK_zpow (p := ℓ) (poleZ (3 * ℓ - 1) a))
      have e : ((tl ℓ : ℚ) : Qt n) * -((dPrime (3 * ℓ - 1) a : Qt n) * (sgnPole (poleZ (3 * ℓ - 1) a) : Qt n) *
          (zK n) ^ poleZ (3 * ℓ - 1) a) =
          -(((tl ℓ : ℚ) : Qt n) * ((dPrime (3 * ℓ - 1) a : ℚ) : Qt n) * (sgnPole (poleZ (3 * ℓ - 1) a) : Qt n) *
            (zK n) ^ poleZ (3 * ℓ - 1) a) := by
        ring
      rw [e]
      refine vGe_neg ?_
      convert h3 using 2
      norm_num
    · rw [mul_zero]; exact vGe_zero 0
  have e : (GramF n (3 * ℓ - 1) a b).comp (C ((tl ℓ : ℚ) : Qt n) * X) =
      C (Afun n (3 * ℓ - 1) (fLag (3 * ℓ - 1) a * fLag (3 * ℓ - 1) b)) +
        X * C (((tl ℓ : ℚ) : Qt n) * Bfun n (3 * ℓ - 1) (fLag (3 * ℓ - 1) a * fLag (3 * ℓ - 1) b)) := by
    simp only [GramF, LamX, add_comp, C_comp, mul_comp, X_comp, C_mul]
    ring
  rw [e]
  exact vGeX_add (vGeX_C (vGe_of_pInt hA)) (vGeX_X_mul (vGeX_C hB))

end S

/-- Step 6: `v_ℓ(c_k) ≥ −2K + 2k`. -/
theorem lemmaP_coeff_le [Fact ℓ.Prime] (hℓ : 7 ≤ ℓ) (hℓm : ¬ ℓ ∣ 2 * n) (k : ℕ) :
    padicNorm ℓ ((Delta n (3 * ℓ - 1)).coeff k) ≤ (ℓ : ℚ) ^ ((2 * (3 * ℓ) : ℤ) - 2 * k) := by
  have hℓ2 : ℓ ≠ 2 := by omega
  have hh : Even (3 * ℓ - 1) := by
    obtain ⟨k, hk⟩ := (Fact.out : ℓ.Prime).odd_of_ne_two hℓ2
    exact ⟨3 * k + 1, by omega⟩
  set t : ℚ := tl ℓ with ht
  set φ := Polynomial.compRingHom (C (t : Qt n) * X)
  have h := congrArg φ (lemmaB hh)
  simp only [map_mul, map_sum] at h
  -- right side has integral coefficients
  have hR : φ (C ((-1 : Qt n) ^ ((3 * ℓ - 1 + 1) * (3 * ℓ - 1) / 2))) *
      ∑ a, ∑ b, φ ((GramF n (3 * ℓ - 1)).adjugate a b) ∈ RX n ℓ := by
    refine (RX n ℓ).mul_mem ?_ ?_
    · show (C _).comp _ ∈ RX n ℓ
      rw [C_comp]
      exact vGeX_C (vGe_of_pInt (pInt_pow (pInt_neg pInt_one) _))
    · have hmat : φ.mapMatrix (GramF n (3 * ℓ - 1)) = (RX n ℓ).subtype.mapMatrix
          (fun a b => ⟨φ (GramF n (3 * ℓ - 1) a b), (show φ (GramF n (3 * ℓ - 1) a b) ∈ RX n ℓ from
            GramF_comp_mem hℓm a b)⟩) := by
        exact Matrix.ext fun a b => rfl
      have e : ∀ a b, φ ((GramF n (3 * ℓ - 1)).adjugate a b) = (φ.mapMatrix (GramF n (3 * ℓ - 1))).adjugate a b := by
        intro a b; rw [← RingHom.map_adjugate]; rfl
      set M : Matrix (Fin (3 * ℓ - 1 + 1)) (Fin (3 * ℓ - 1 + 1)) (RX n ℓ) :=
        fun a b => ⟨φ (GramF n (3 * ℓ - 1) a b), (show φ (GramF n (3 * ℓ - 1) a b) ∈ RX n ℓ from
            GramF_comp_mem hℓm a b)⟩ with hM
      have e2 : ∀ a b, ((RX n ℓ).subtype.mapMatrix M).adjugate a b = (RX n ℓ).subtype (M.adjugate a b) := by
        intro a b; rw [← RingHom.map_adjugate]; rfl
      simp only [e, hmat, e2]
      refine (RX n ℓ).sum_mem (fun a _ => (RX n ℓ).sum_mem (fun b _ => ?_))
      exact (M.adjugate a b).2
  rw [← h] at hR
  have hk := hR k
  have e : (φ ((Delta n (3 * ℓ - 1)).map (algebraMap ℚ (Qt n))) *
      φ (C (∏ i ∈ range (3 * ℓ - 1 + 1), ((dPrime (3 * ℓ - 1) i : ℚ) : Qt n)))).coeff k =
      ((((Delta n (3 * ℓ - 1)).coeff k * t ^ k * ∏ i ∈ range (3 * ℓ - 1 + 1), dPrime (3 * ℓ - 1) i : ℚ)) : Qt n) := by
    show (((Delta n (3 * ℓ - 1)).map (algebraMap ℚ (Qt n))).comp (C (t : Qt n) * X) *
      (C (∏ i ∈ range (3 * ℓ - 1 + 1), ((dPrime (3 * ℓ - 1) i : ℚ) : Qt n))).comp (C (t : Qt n) * X)).coeff k = _
    rw [C_comp, coeff_mul_C, comp_C_mul_X_coeff, coeff_map, eq_ratCast]
    push_cast; ring
  rw [e] at hk
  have hn := padicNorm_le_of_vGe (p := ℓ) hk
  rw [neg_zero, zpow_zero, padicNorm.mul, padicNorm.mul, padicNorm_pow'] at hn
  have hP0 : ∏ i ∈ range (3 * ℓ - 1 + 1), dPrime (3 * ℓ - 1) i ≠ 0 :=
    prod_ne_zero_iff.mpr (fun i _ => LB.dPrime_ne_zero _ _)
  rw [padicNorm.eq_zpow_of_nonzero hP0, padicValRat_prod_dPrime hℓ2] at hn
  have hl0 : (0 : ℚ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).pos
  rw [ht, padicNorm_tl] at hn
  set A := padicNorm ℓ ((Delta n (3 * ℓ - 1)).coeff k)
  have hpos : (0 : ℚ) < ((ℓ : ℚ) ^ (2 : ℤ)) ^ k * (ℓ : ℚ) ^ (-(2 * (3 * (ℓ : ℤ)))) := by positivity
  have key : A ≤ 1 / (((ℓ : ℚ) ^ (2 : ℤ)) ^ k * (ℓ : ℚ) ^ (-(2 * (3 * (ℓ : ℤ))))) := by
    rw [le_div_iff₀ hpos, ← mul_assoc]; exact hn
  refine key.trans (le_of_eq ?_)
  rw [one_div, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hl0.ne', ← zpow_neg]
  congr 1; push_cast; ring

/-- **Lemma P′.** `Δ_{3ℓ−1}(a/b) ≠ 0` whenever `ℓ² ∤ b`. -/
theorem lemmaP [Fact ℓ.Prime] (hℓ : 7 ≤ ℓ) (hℓa : ¬ ℓ ∣ n) (a : ℤ) {b : ℕ} (hb : 0 < b) (hb2 : ¬ ℓ ^ 2 ∣ b) :
    (Delta n (3 * ℓ - 1)).eval ((a : ℚ) / b) ≠ 0 := by
  have hℓm : ¬ ℓ ∣ 2 * n := fun hd => ((Nat.Prime.dvd_mul (Fact.out : ℓ.Prime)).mp hd).elim
    (fun h2 => by have := Nat.le_of_dvd two_pos h2; omega) hℓa
  have hl : (1 : ℚ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  have hl0 : (0 : ℚ) < ℓ := by linarith
  set K2 : ℤ := 2 * (3 * ℓ) with hK2
  obtain ⟨hv0, hc0⟩ := lemmaP_coeff_zero hℓ hℓm
  have hn0 : padicNorm ℓ ((Delta n (3 * ℓ - 1)).coeff 0) = (ℓ : ℚ) ^ K2 := by
    rw [padicNorm.eq_zpow_of_nonzero hc0, hv0, neg_neg]
  -- `|a/b|_ℓ ≤ ℓ`
  have hab : padicNorm ℓ ((a : ℚ) / b) ≤ ℓ := by
    rw [padicNorm.div]
    have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    have hvb : padicValRat ℓ (b : ℚ) ≤ 1 := by
      rw [padicValRat.of_nat]
      by_contra hc
      push Not at hc
      exact hb2 ((padicValNat_dvd_iff_le hb.ne').mpr (by omega))
    have hbn : (ℓ : ℚ) ^ (-1 : ℤ) ≤ padicNorm ℓ (b : ℚ) := by
      rw [padicNorm.eq_zpow_of_nonzero hb0]
      exact zpow_le_zpow_right₀ hl.le (by omega)
    have hpos : (0 : ℚ) < padicNorm ℓ (b : ℚ) := lt_of_lt_of_le (by positivity) hbn
    rw [div_le_iff₀ hpos]
    calc padicNorm ℓ (a : ℚ) ≤ 1 := padicNorm.of_int a
      _ = (ℓ : ℚ) * (ℓ : ℚ) ^ (-1 : ℤ) := by rw [zpow_neg_one, mul_inv_cancel₀ hl0.ne']
      _ ≤ (ℓ : ℚ) * padicNorm ℓ (b : ℚ) := by gcongr
  rw [eval_eq_sum_range, sum_range_succ']
  have htail : padicNorm ℓ (∑ k ∈ range (Delta n (3 * ℓ - 1)).natDegree,
      (Delta n (3 * ℓ - 1)).coeff (k + 1) * ((a : ℚ) / b) ^ (k + 1)) < (ℓ : ℚ) ^ K2 := by
    refine padicNorm.sum_lt' (fun k _ => ?_) (zpow_pos hl0 _)
    rw [padicNorm.mul, padicNorm_pow']
    have h1 := lemmaP_coeff_le hℓ hℓm (k + 1)
    have h2 : padicNorm ℓ ((a : ℚ) / b) ^ (k + 1) ≤ (ℓ : ℚ) ^ (k + 1) :=
      pow_le_pow_left₀ (padicNorm.nonneg _) hab _
    calc padicNorm ℓ ((Delta n (3 * ℓ - 1)).coeff (k + 1)) * padicNorm ℓ ((a : ℚ) / b) ^ (k + 1)
        ≤ (ℓ : ℚ) ^ (K2 - 2 * ((k + 1 : ℕ) : ℤ)) * (ℓ : ℚ) ^ (k + 1) :=
          mul_le_mul h1 h2 (pow_nonneg (padicNorm.nonneg _) _) (zpow_pos hl0 _).le
      _ = (ℓ : ℚ) ^ (K2 - ((k + 1 : ℕ) : ℤ)) := by
          rw [← zpow_natCast, ← zpow_add₀ hl0.ne']; congr 1; ring
      _ < (ℓ : ℚ) ^ K2 := zpow_lt_zpow_right₀ hl (by omega)
  have hne : padicNorm ℓ (∑ k ∈ range (Delta n (3 * ℓ - 1)).natDegree,
      (Delta n (3 * ℓ - 1)).coeff (k + 1) * ((a : ℚ) / b) ^ (k + 1)) ≠
      padicNorm ℓ ((Delta n (3 * ℓ - 1)).coeff 0 * ((a : ℚ) / b) ^ 0) := by
    rw [pow_zero, mul_one, hn0]; exact htail.ne
  intro h0
  have hmax := padicNorm.add_eq_max_of_ne hne
  rw [h0, padicNorm.zero, pow_zero, mul_one, hn0] at hmax
  have : (0 : ℚ) < (ℓ : ℚ) ^ K2 := zpow_pos hl0 _
  have := le_max_right (padicNorm ℓ (∑ k ∈ range (Delta n (3 * ℓ - 1)).natDegree,
      (Delta n (3 * ℓ - 1)).coeff (k + 1) * ((a : ℚ) / b) ^ (k + 1))) ((ℓ : ℚ) ^ K2)
  linarith

/-- Infinitely many even `h` with `Δ_h(a/b) ≠ 0` (primes `ℓ > n`, so `ℓ ∤ n`). -/
theorem nonvan_frequently (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ∃ᶠ h : ℕ in atTop, Even h ∧ (Delta n h).eval ((a : ℚ) / b) ≠ 0 := by
  rw [frequently_atTop]
  intro N
  obtain ⟨ℓ, hℓN, hℓp⟩ := Nat.exists_infinite_primes (N + b + 7 + 2 * n)
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have hℓ7 : 7 ≤ ℓ := by omega
  have hodd : Odd ℓ := hℓp.odd_of_ne_two (by omega)
  have hm1 := (Fact.out : 3 ≤ n)
  have hℓm : ¬ ℓ ∣ n := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  refine ⟨3 * ℓ - 1, by omega, ?_, lemmaP hℓ7 hℓm a hb ?_⟩
  · obtain ⟨k, rfl⟩ := hodd
    exact ⟨3 * k + 1, by omega⟩
  · intro hdvd
    have hle := Nat.le_of_dvd hb hdvd
    have : ℓ ≤ ℓ ^ 2 := Nat.le_self_pow (by norm_num) ℓ
    omega

end LP
end Ti
end Chi2U
