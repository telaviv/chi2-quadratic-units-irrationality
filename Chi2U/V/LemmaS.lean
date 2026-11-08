/-
# Lemma S (PROOF_V §3.2): `n_p ≤ Σ_{l ≥ 1, p^l ≤ h} A_K(p^l) + v_p(m)·(h/2 − 1)²` for odd `p`

**Statement** (`lemmaS_proof`, the exact statement of `lemmaS` in `Interface.lean`): for an odd prime `p ∣ m` and even `h`, every
coefficient of `Δ_h` satisfies `|c_k|_p ≤ p^{eS m h p}`. The proof never uses `p ∣ m`: for `p ∤ 2m` it is the general
multi-level Lemma 8′ of PROOF_U (`e = 0`).

**Route.** PROOF_U's Lemma 7′ expands `Δ_h = det(𝒫 + Vᵀ diag(γ) V)` by Laplace and Cauchy–Binet. Here:
* `det H = det [[𝒫, Vᵀ], [−diag(γ)V, 1]]` (Schur complement, `SHankel.det_HkM_eq_BlkM`) and the multilinear
  expansion of the `K` bottom rows (`SMatrix.det_expand_rows`) give `det H = Σ_S (Π_{a∈S} γ_a)·det N_S`;
* `N_S = L Ñ_S Lᵀ`, `L = diag(1, E)`, with the Newton matrix `E` (`SNewton`), so `det N_S = Vand(x_S)²·det Ñ_S` and
  `Ñ_S = [[𝒫, W₂ᵀ], [−W₁, I_{S^c}]]` has integral entries outside `𝒫`;
* `v_p(𝒫_{ij}) ≥ −e(i + j − K)₊ ≥ −e((i − J)₊ + (j − J − 1)₊)` (Mahler form, `SVal.vGe_muPoly_divD`), so by Leibniz with
  row and column exponents `v_p(det Ñ_S) ≥ −e(J − 1)²` (`SCount.sum_trunc_sq`), `e = v_p(m)`, `J = h/2`;
* `v_p(γ_a) ≥ −v_p(D′(x_a)) − wT(a)` (`SVal.vGe_Psum_levels`), and
  `Σ_{a∈S} v_p(D′(x_a)) − 2 v_p(Vand(x_S)) = Σ_{a∈S, l∉S} v_p(x_a − x_l)` (`SCount.sum_pairs_split`);
* the class count `Σ_{a∈S, l∉S} v_p(x_a − x_l) + Σ_{a∈S} wT(a) ≤ Σ_l A_K(p^l)` (`SCount.cost_le`).
Departure from PROOF_V: the bound `v_p(𝒫_{ij}) ≥ −e(i + j − K)₊` is used without the `v_p(b!)` refinement, and the
factor `(i + σ(i) − K)₊ ≤ (i − K/2)₊ + (σ(i) − K/2)₊` is replaced by integer row/column exponents with the same total.
-/
import Chi2U.V.SHankel
import Chi2U.V.AKSize

namespace Chi2U
namespace V
namespace LS

open Polynomial Finset Matrix

lemma padicValRat_finset_prod {ι : Type*} {p : ℕ} [Fact p.Prime] (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, f i ≠ 0) : padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [prod_insert ha, sum_insert ha, padicValRat.mul (hf a (mem_insert_self a s))
        (prod_ne_zero_iff.mpr (fun i hi => hf i (mem_insert_of_mem hi))),
        ih (fun i hi => hf i (mem_insert_of_mem hi))]

section Term

variable (m : ℕ) [Fact (1 ≤ m)] (h : ℕ)

/-- `ℤ → ℚ(√d)[X]`. -/
noncomputable abbrev iZ : ℤ →+* (Qd m)[X] := Int.castRingHom (Qd m)[X]

/-- The atoms of a term. -/
def atomsOf (T : Finset (Fin h ⊕ Fin (h + 1))) : Finset (Fin (h + 1)) := univ.filter (fun a => Sum.inr a ∈ T)

lemma eq_map_atomsOf {T : Finset (Fin h ⊕ Fin (h + 1))} (hT : T ⊆ botRows h) :
    T = (atomsOf h T).map ⟨Sum.inr, Sum.inr_injective⟩ := by
  ext r
  rcases r with i | a
  · simp only [mem_map, Function.Embedding.coeFn_mk, reduceCtorEq, and_false, exists_false, iff_false]
    intro hi
    obtain ⟨b, -, hb⟩ := mem_map.mp (hT hi)
    exact Sum.inr_ne_inl hb
  · simp [atomsOf]

/-- `[a ∈ S] x_a^j`. -/
def botZ (S : Finset (Fin (h + 1))) : Matrix (Fin (h + 1)) (Fin h) ℤ :=
  Matrix.of fun a (j : Fin h) => if a ∈ S then xP h a ^ (j : ℕ) else 0

lemma NT_eq {T : Finset (Fin h ⊕ Fin (h + 1))} (hT : T ⊆ botRows h) :
    NT m h T = fromBlocks (PmM m h) (VmM m h).transpose (-((botZ h (atomsOf h T)).map (iZ m)))
      ((IdS (atomsOf h T)).map (iZ m)) := by
  have hinl : ∀ i : Fin h, Sum.inl i ∉ botRows h := fun i hi => by
    obtain ⟨b, -, hb⟩ := mem_map.mp hi; exact Sum.inr_ne_inl hb
  have hinr : ∀ a : Fin (h + 1), Sum.inr a ∈ botRows h := fun a => mem_map.mpr ⟨a, mem_univ _, rfl⟩
  refine Matrix.ext (fun r c => ?_)
  rcases r with i | a
  · have hi : Sum.inl i ∉ T := fun h' => hinl i (hT h')
    rcases c with j | b <;> simp [NT, hi, hinl, BlkM]
  · by_cases ha : Sum.inr a ∈ T
    · have ha' : a ∈ atomsOf h T := by simp [atomsOf, ha]
      rcases c with j | b
      · simp [NT, ha, uRow, botZ, ha', VmM]
      · simp [NT, ha, uRow, IdS, ha', Matrix.diagonal_apply]
    · have ha' : a ∉ atomsOf h T := by simp [atomsOf, ha]
      rcases c with j | b
      · simp [NT, ha, hinr, wRow, botZ, ha']
      · simp [NT, ha, hinr, wRow, IdS, ha', Matrix.diagonal_apply]

/-- `Ñ_S = [[𝒫, W₂ᵀ], [−W₁, I_{S^c}]]`. -/
noncomputable def NtilM (S : Finset (Fin (h + 1))) : Matrix (Fin h ⊕ Fin (h + 1)) (Fin h ⊕ Fin (h + 1)) (Qd m)[X] :=
  fromBlocks (PmM m h) ((W2 (xP h) S h).map (iZ m)).transpose (-((W1 (xP h) S h).map (iZ m))) ((IdS S).map (iZ m))

/-- `L = diag(1, E)`. -/
noncomputable def LM (S : Finset (Fin (h + 1))) : Matrix (Fin h ⊕ Fin (h + 1)) (Fin h ⊕ Fin (h + 1)) (Qd m)[X] :=
  fromBlocks 1 0 0 ((Emat (xP h) S).map (iZ m))

lemma factor_eq (S : Finset (Fin (h + 1))) :
    fromBlocks (PmM m h) (VmM m h).transpose (-((botZ h S).map (iZ m))) ((IdS S).map (iZ m)) =
      LM m h S * NtilM m h S * (LM m h S).transpose := by
  have hE1 : (Emat (xP h) S).map (iZ m) * (W1 (xP h) S h).map (iZ m) = (botZ h S).map (iZ m) := by
    rw [← Matrix.map_mul, Emat_mul_W1]; rfl
  have hE2 : (Emat (xP h) S).map (iZ m) * (W2 (xP h) S h).map (iZ m) = VmM m h := by
    rw [← Matrix.map_mul, Emat_mul_W2]
    ext a j : 1
    simp [VmM]
  have hE3 : (Emat (xP h) S).map (iZ m) * (IdS S).map (iZ m) * ((Emat (xP h) S).map (iZ m)).transpose =
      (IdS S).map (iZ m) := by
    rw [← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, Emat_IdS]
  rw [LM, NtilM, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.mul_zero,
    Matrix.transpose_zero, Matrix.transpose_one, Matrix.mul_neg, neg_zero]
  rw [← Matrix.transpose_mul, hE1, hE2, hE3]

/-- The Vandermonde product of `x_S`. -/
def vandZ (S : Finset (Fin (h + 1))) : ℤ := ∏ a ∈ S, ∏ k ∈ S.filter (· < a), (xP h a - xP h k)

lemma det_NT {T : Finset (Fin h ⊕ Fin (h + 1))} (hT : T ⊆ botRows h) :
    (NT m h T).det = iZ m (vandZ h (atomsOf h T)) * (NtilM m h (atomsOf h T)).det *
      iZ m (vandZ h (atomsOf h T)) := by
  rw [NT_eq m h hT, factor_eq, det_mul, det_mul, det_transpose, LM, det_fromBlocks_zero₂₁, det_one, one_mul,
    vandZ, ← det_Emat, RingHom.map_det, RingHom.mapMatrix_apply]

end Term

section Val

variable {m : ℕ} [Fact (1 ≤ m)] {h : ℕ} {p : ℕ} [hpF : Fact p.Prime]

/-- `e = v_p(2m)`. -/
noncomputable abbrev eV (m p : ℕ) : ℤ := padicValRat p ((2 * m : ℕ) : ℚ)

lemma eV_nonneg : 0 ≤ eV m p := by unfold eV; rw [padicValRat.of_nat]; positivity

lemma eV_eq (hp : p ≠ 2) : eV m p = padicValNat p m := by
  have hm : m ≠ 0 := by have := (Fact.out : 1 ≤ m); omega
  unfold eV
  rw [padicValRat.of_nat, padicValNat.mul two_ne_zero hm,
    padicValNat.eq_zero_of_not_dvd (fun hd => hp ((Nat.prime_dvd_prime_iff_eq hpF.out Nat.prime_two).mp hd))]
  simp

/-- Row and column exponents of `Ñ_S`. -/
noncomputable def rhoE (m h p : ℕ) : Fin h ⊕ Fin (h + 1) → ℤ :=
  Sum.elim (fun i => -(eV m p * (((i : ℕ) - h / 2 : ℕ) : ℤ))) (fun _ => 0)

noncomputable def kapE (m h p : ℕ) : Fin h ⊕ Fin (h + 1) → ℤ :=
  Sum.elim (fun j => -(eV m p * (((j : ℕ) - h / 2 - 1 : ℕ) : ℤ))) (fun _ => 0)

lemma rhoE_nonpos (r : Fin h ⊕ Fin (h + 1)) : rhoE m h p r ≤ 0 := by
  rcases r with i | a
  · simp only [rhoE, Sum.elim_inl, neg_nonpos]; exact mul_nonneg eV_nonneg (Nat.cast_nonneg _)
  · simp [rhoE]

lemma kapE_nonpos (r : Fin h ⊕ Fin (h + 1)) : kapE m h p r ≤ 0 := by
  rcases r with i | a
  · simp only [kapE, Sum.elim_inl, neg_nonpos]; exact mul_nonneg eV_nonneg (Nat.cast_nonneg _)
  · simp [kapE]

lemma vGeX_iZ (z : ℤ) : vGeX p 0 (iZ m z) := vGeX_intCast z

lemma vGeX_Ntil (hh : Even h) (S : Finset (Fin (h + 1))) (r c : Fin h ⊕ Fin (h + 1)) :
    vGeX p (rhoE m h p r + kapE m h p c) (NtilM m h S r c) := by
  rcases r with i | a <;> rcases c with j | b
  · -- the polynomial part
    simp only [NtilM, fromBlocks_apply₁₁, PmM, Matrix.of_apply, rhoE, kapE, Sum.elim_inl]
    refine vGeX_C (vGe_mono ?_ (vGe_muPoly_divD (mz := m) (p := p) h ((i : ℕ) + j)))
    obtain ⟨J, hJ⟩ := hh
    have hJ2 : h / 2 = J := by omega
    rw [hJ2]
    have hi := i.isLt
    have hj := j.isLt
    have hle : ((i : ℕ) + j - (h + 1) : ℕ) ≤ ((i : ℕ) - J : ℕ) + ((j : ℕ) - J - 1 : ℕ) := by omega
    have hle' : ((((i : ℕ) + j - (h + 1) : ℕ)) : ℤ) ≤ (((i : ℕ) - J : ℕ) : ℤ) + (((j : ℕ) - J - 1 : ℕ) : ℤ) := by
      exact_mod_cast hle
    have := mul_le_mul_of_nonneg_left hle' (eV_nonneg (m := m) (p := p))
    unfold eV at this ⊢
    linarith
  · simp only [NtilM, fromBlocks_apply₁₂, Matrix.transpose_apply, Matrix.map_apply]
    exact vGeX_mono (by have := rhoE_nonpos (m := m) (p := p) (Sum.inl i); simpa [kapE] using this)
      (vGeX_iZ _)
  · simp only [NtilM, fromBlocks_apply₂₁, Matrix.neg_apply, Matrix.map_apply]
    exact vGeX_neg (vGeX_mono (by have := kapE_nonpos (m := m) (p := p) (Sum.inl j); simpa [rhoE] using this)
      (vGeX_iZ _))
  · simp only [NtilM, fromBlocks_apply₂₂, Matrix.map_apply]
    exact vGeX_mono (by simp [rhoE, kapE]) (vGeX_iZ _)

lemma sum_rho_kap (hh : Even h) :
    ∑ r, rhoE m h p r + ∑ c, kapE m h p c = -(eV m p * (((h / 2 - 1) ^ 2 : ℕ) : ℤ)) := by
  obtain ⟨J, hJ⟩ := hh
  have hJ2 : h / 2 = J := by omega
  have hh2 : h = 2 * J := by omega
  simp only [Fintype.sum_sum_type, rhoE, kapE, Sum.elim_inl, Sum.elim_inr, sum_const_zero, add_zero]
  rw [Fin.sum_univ_eq_sum_range (fun i => -(eV m p * (((i : ℕ) - h / 2 : ℕ) : ℤ))) h,
    Fin.sum_univ_eq_sum_range (fun j => -(eV m p * (((j : ℕ) - h / 2 - 1 : ℕ) : ℤ))) h, ← sum_add_distrib]
  rw [hJ2, ← sum_trunc_sq J]
  push_cast
  rw [hh2, mul_add, mul_sum, mul_sum, neg_add, ← sum_neg_distrib, ← sum_neg_distrib, ← sum_add_distrib]

lemma vGeX_det_Ntil (hh : Even h) (S : Finset (Fin (h + 1))) :
    vGeX p (-(eV m p * (((h / 2 - 1) ^ 2 : ℕ) : ℤ))) (NtilM m h S).det := by
  rw [← sum_rho_kap (m := m) (p := p) hh]
  exact vGeX_det_rc _ _ _ (vGeX_Ntil hh S)

lemma vGeX_gamF (hh : Even h) {a : ℕ} (ha : a ≤ h) :
    vGeX p (-padicValRat p (dPrime h a) - wT h p a) (gamF m h a) := by
  unfold gamF
  have h1 : vGe p (-padicValRat p (dPrime h a)) ((((dPrime h a)⁻¹ : ℚ) : Qd m) * (zK m) ^ (poleZ h a)) := by
    have := vGe_mul (vGe_ratCast (mz := m) (p := p) (dPrime h a)⁻¹) (vGe_zK_zpow (mz := m) (p := p) (poleZ h a))
    rwa [padicValRat.inv, add_zero] at this
  have h2 : vGeX p (-(wT h p a : ℤ)) (C (Psum m (poleZ h a)) - X) := by
    rw [sub_eq_add_neg]
    exact vGeX_add (vGeX_C (vGe_Psum_levels hh ha)) (vGeX_neg (vGeX_mono (by simp) vGeX_X))
  have := vGeX_mul (vGeX_C h1) h2
  rwa [← sub_eq_add_neg] at this

lemma padicValRat_vandZ (hp : p ≠ 2) (S : Finset (Fin (h + 1))) :
    padicValRat p ((vandZ h S : ℤ) : ℚ) =
      ∑ a ∈ S, ∑ k ∈ S.filter (· < a), (vmult h p a k : ℤ) := by
  unfold vandZ
  push_cast
  rw [padicValRat_finset_prod _ _ (fun a _ => prod_ne_zero_iff.mpr (fun k hk => sub_ne_zero.mpr (fun e => by
    have := (mem_filter.mp hk).2
    have e' : poleZ h a = poleZ h k := by exact_mod_cast e
    unfold poleZ at e'
    exact absurd (Fin.ext (by omega)) (ne_of_gt this))))]
  refine sum_congr rfl (fun a _ => ?_)
  rw [padicValRat_finset_prod _ _ (fun k hk => sub_ne_zero.mpr (fun e => by
    have := (mem_filter.mp hk).2
    have e' : poleZ h a = poleZ h k := by exact_mod_cast e
    unfold poleZ at e'
    exact absurd (Fin.ext (by omega)) (ne_of_gt this)))]
  refine sum_congr rfl (fun k hk => ?_)
  have hka := (mem_filter.mp hk).2
  exact padicValRat_pole_sub hp (Nat.lt_succ_iff.mp a.isLt) (Nat.lt_succ_iff.mp k.isLt)
    (fun e => absurd (Fin.ext e) (ne_of_gt hka))

end Val

section Main

variable {m : ℕ} [Fact (1 ≤ m)] {h : ℕ} {p : ℕ} [hpF : Fact p.Prime]

lemma map_val_subset (S : Finset (Fin (h + 1))) : S.map Fin.valEmbedding ⊆ range (h + 1) := fun n hn => by
  obtain ⟨a, -, rfl⟩ := mem_map.mp hn
  exact mem_range.mpr a.isLt

lemma filter_lt_map (S : Finset (Fin (h + 1))) (a : Fin (h + 1)) :
    (S.filter (· < a)).map Fin.valEmbedding = (S.map Fin.valEmbedding).filter (· < (a : ℕ)) := by
  rw [filter_map]
  congr 1

lemma vGeX_iZ_val (z : ℤ) : vGeX p (padicValRat p (z : ℚ)) (iZ m z) := by
  have := vGeX_C (vGe_ratCast (mz := m) (p := p) (z : ℚ))
  rw [show (((z : ℚ)) : Qd m) = (z : Qd m) from Rat.cast_intCast z, C_eq_intCast] at this
  exact this

/-- The exponent of a term is at least `−eS`. -/
lemma exponent_bound (hp : p ≠ 2) (S : Finset (Fin (h + 1))) :
    -(eS m h p : ℤ) ≤ ∑ a ∈ S, (-padicValRat p (dPrime h a) - wT h p a) +
      (padicValRat p ((vandZ h S : ℤ) : ℚ) + -(eV m p * (((h / 2 - 1) ^ 2 : ℕ) : ℤ)) +
        padicValRat p ((vandZ h S : ℤ) : ℚ)) := by
  set Sn := S.map Fin.valEmbedding with hSn
  have hSsub := map_val_subset S
  have hsplit := sum_pairs_split (range (h + 1)) Sn hSsub (vmult h p) (vmult_comm h p)
  have hcost := cost_le (h := h) hpF.out.pos Sn hSsub
  have e1 : ∑ a ∈ S, padicValRat p (dPrime h a) =
      ((∑ n ∈ Sn, ∑ l ∈ range (h + 1), (if l = n then 0 else vmult h p n l) : ℕ) : ℤ) := by
    rw [Nat.cast_sum, hSn, sum_map]
    refine sum_congr rfl (fun a _ => ?_)
    rw [padicValRat_dPrime hp (Nat.lt_succ_iff.mp a.isLt)]
    push_cast
    rfl
  have e2 : ∑ a ∈ S, (wT h p a : ℤ) = ((∑ n ∈ Sn, wT h p n : ℕ) : ℤ) := by
    rw [Nat.cast_sum, hSn, sum_map]; rfl
  have e3 : padicValRat p ((vandZ h S : ℤ) : ℚ) =
      ((∑ n ∈ Sn, ∑ k ∈ Sn.filter (· < n), vmult h p n k : ℕ) : ℤ) := by
    rw [padicValRat_vandZ hp, Nat.cast_sum, hSn, sum_map]
    refine sum_congr rfl (fun a _ => ?_)
    rw [Fin.valEmbedding_apply, ← filter_lt_map, Nat.cast_sum, sum_map]
    rfl
  rw [sum_sub_distrib, sum_neg_distrib, e1, e2, e3, eV_eq hp]
  unfold eS
  have hsplit' := congrArg (fun n : ℕ => (n : ℤ)) hsplit
  have hcost' : (((∑ m ∈ Sn, ∑ l ∈ range (h + 1) \ Sn, vmult h p m l + ∑ m ∈ Sn, wT h p m : ℕ)) : ℤ) ≤
      ((∑ e ∈ levelsV h p, AK h (p ^ e) : ℕ) : ℤ) := by exact_mod_cast hcost
  push_cast at hsplit' hcost' ⊢
  linarith

lemma term_bound (hp : p ≠ 2) (hh : Even h) {T : Finset (Fin h ⊕ Fin (h + 1))} (hT : T ∈ (botRows h).powerset) :
    vGeX p (-(eS m h p : ℤ)) ((∏ r ∈ T, aRow m h r) * (NT m h T).det) := by
  have hT' := mem_powerset.mp hT
  have hprod : ∏ r ∈ T, aRow m h r = ∏ a ∈ atomsOf h T, gamF m h a := by
    conv_lhs => rw [eq_map_atomsOf h hT']
    rw [prod_map]
    rfl
  rw [hprod, det_NT m h hT']
  exact vGeX_mono (exponent_bound hp (atomsOf h T))
    (vGeX_mul (vGeX_prod _ _ _ (fun a _ => vGeX_gamF hh (Nat.lt_succ_iff.mp a.isLt)))
      (vGeX_mul (vGeX_mul (vGeX_iZ_val _) (vGeX_det_Ntil hh _)) (vGeX_iZ_val _)))

end Main

end LS

open LS Polynomial Finset

/-- **Lemma S** (PROOF_V §3.2): for an odd prime `p ∣ m`, `n_p ≤ Σ_{l ≥ 1, p^l ≤ h} A_K(p^l) + e(h/2 − 1)²`,
`e = v_p(m)`. (The hypothesis `p ∣ m` is not used: for `p ∤ m` this is the multi-level Lemma 8′.) -/
theorem lemmaS_proof (m : ℕ) [Fact (1 ≤ m)] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hpm : p ∣ m) {h : ℕ} (hh : Even h)
    (k : ℕ) : padicNorm p ((Delta m h).coeff k) ≤ (p : ℚ) ^ eS m h p := by
  have hX : vGeX p (-(eS m h p : ℤ)) ((Delta m h).map (algebraMap ℚ (Qd m))) := by
    rw [Delta_map hh]
    change vGeX p _ (HkM m h).det
    rw [det_HkM_expand]
    exact vGeX_sum _ _ (fun T hT => term_bound hp hh hT)
  have := padicNorm_coeff_of_vGeX_map hX k
  rwa [neg_neg, zpow_natCast] at this

end V
end Chi2U
