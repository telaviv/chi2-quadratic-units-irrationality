/-
# Lemma 10′ (2-adic bound), part 2: the entries `G_{ij}` in the anchored basis (PROOF_U §4)

Back in the variable `t = 2τ`: `(a_i b_j)(t/2) = 2^{−(i+j)} · ∏_{m ∈ Z}(t − x_m)` with
`Z = {m < i} ∪ {h+1−j ≤ m ≤ h}` (`gAB_comp`), so `G = 2^{h+2−i−j} Λ_X(∏_Z (t − x_m))` (`GA_eq`, `GB_eq`).
* (L) `i + j ≥ K = h + 1`: `∏_Z = D · F`, `F = ∏_{h+1−j ≤ m < i}(t − x_m) ∈ ℤ[t]` of degree `π = i + j − K`, so
  `B = 0` and `A = μ(F) = Lmom(F′)`; the Mahler form (`Mahler.Lmom_eq_mahler`) with `2^b b! ∣ Δ^b[F′(2s+1)](0)`
  and `v₂(4^{−(b+1)}) = −2(b+1)` gives `v₂(Lmom F′) ≥ −⌊log₂ π⌋ − 3` (`vGe_Lmom_int`).
* (U) `N₀ = h − i − j ≥ 0`: the polynomial part vanishes and the residues are
  `c_{i+l} = (−1)^{N₀−l} C(N₀,l)/(2^{N₀} N₀!)` (`sum_U`), so
  `G_A = (4/N₀!) Δ^{N₀}[z^{x_{i+l}} P(x_{i+l})](0)`, `G_B = −(4/N₀!) Δ^{N₀}[z^{x_{i+l}}](0)` (`GA_U`, `GB_U`);
  the sequence `T(l) = z^{x_{i+l}} P(x_{i+l})` satisfies `T(l+1) = z² T(l) − z/(x_i + 1 + 2l)²` (from
  `P(x+2) = P(x) − z^{−x−1}/(x+1)²`, `Psum_add_two`), and `v₂(z² − 1) = v₂(−4z) = 2`, so `vGe_fd_seq` applies.
-/
import Chi2U.Arith.TwoAdicBasis
import Chi2U.Arith.TwoAdicDefs
import Chi2U.Mahler

namespace Chi2U.TwoAdicAux

open Polynomial Finset fwdDiff
open scoped Nat

variable {h : ℕ}

/-! ### Products over the poles -/

/-- `∏_{m ∈ s} (t − x_m)`. -/
noncomputable def PZ (h : ℕ) (s : Finset ℕ) : ℚ[X] := ∏ m ∈ s, (X - C ((poleZ h m : ℤ) : ℚ))

/-- The same product over `ℤ`. -/
noncomputable def PZint (h : ℕ) (s : Finset ℕ) : ℤ[X] := ∏ m ∈ s, (X - C (poleZ h m))

lemma PZ_eq_map (h : ℕ) (s : Finset ℕ) : PZ h s = (PZint h s).map (Int.castRingHom ℚ) := by
  unfold PZ PZint; rw [Polynomial.map_prod]; simp

lemma PZ_monic (h : ℕ) (s : Finset ℕ) : (PZ h s).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

lemma natDegree_PZ (h : ℕ) (s : Finset ℕ) : (PZ h s).natDegree = s.card := by
  unfold PZ
  rw [natDegree_prod_of_monic _ _ (fun m _ => monic_X_sub_C _),
    sum_congr rfl (fun m _ => natDegree_X_sub_C _), sum_const, smul_eq_mul, mul_one]

lemma Dpoly_eq_PZ (h : ℕ) : Dpoly h = PZ h (range (h + 1)) := rfl

lemma eval_PZ (h : ℕ) (s : Finset ℕ) (k : ℕ) :
    (PZ h s).eval ((poleZ h k : ℤ) : ℚ) = ∏ m ∈ s, (((poleZ h k : ℤ) : ℚ) - poleZ h m) := by
  unfold PZ; rw [eval_prod]; simp only [eval_sub, eval_X, eval_C]

lemma eval_PZ_eq_zero {s : Finset ℕ} {k : ℕ} (hk : k ∈ s) : (PZ h s).eval ((poleZ h k : ℤ) : ℚ) = 0 := by
  rw [eval_PZ]; exact prod_eq_zero hk (sub_self _)

lemma poleZ_sub (h a b : ℕ) : ((poleZ h a : ℤ) : ℚ) - poleZ h b = 2 * ((a : ℚ) - b) := by
  unfold poleZ; push_cast; ring

lemma poleZ_sub_ne_zero {a b : ℕ} (hab : a ≠ b) : ((poleZ h a : ℤ) : ℚ) - poleZ h b ≠ 0 := by
  rw [poleZ_sub]
  refine mul_ne_zero two_ne_zero (sub_ne_zero.mpr ?_)
  exact_mod_cast hab

lemma poleZ_add (h i l : ℕ) : poleZ h (i + l) = poleZ h i + 2 * (l : ℤ) := by unfold poleZ; push_cast; ring

/-! ### The rescaling `τ = t/2` -/

lemma two_mul_xiPole (h k : ℕ) : 2 * xiPole h k = ((poleZ h k : ℤ) : ℚ) := by
  unfold xiPole poleZ
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat]

lemma lin_comp_half (a : ℚ) : (X - C a).comp (C (1 / 2) * X) = C (1 / 2) * (X - C (2 * a)) := by
  simp only [sub_comp, X_comp, C_comp]
  rw [mul_sub, ← C_mul]
  congr 2; ring

lemma aAnch_comp (h i : ℕ) : (aAnch h i).comp (C (1 / 2) * X) = C ((1 / 2) ^ i) * PZ h (range i) := by
  unfold aAnch PZ
  rw [Polynomial.prod_comp]
  simp_rw [lin_comp_half, two_mul_xiPole]
  rw [prod_mul_distrib, prod_const, card_range, C_pow]

lemma prod_reflect_Ico (f : ℕ → ℚ[X]) {h j : ℕ} (hj : j ≤ h + 1) :
    ∏ l ∈ range j, f (h - l) = ∏ m ∈ Ico (h + 1 - j) (h + 1), f m := by
  refine Finset.prod_nbij' (fun l => h - l) (fun m => h - m) ?_ ?_ ?_ ?_ ?_
  · intro l hl; simp only [mem_range] at hl; simp only [mem_Ico]; omega
  · intro m hm; simp only [mem_Ico] at hm; simp only [mem_range]; omega
  · intro l hl; simp only [mem_range] at hl; omega
  · intro m hm; simp only [mem_Ico] at hm; omega
  · intro l _; rfl

lemma bAnch_comp (h j : ℕ) (hj : j ≤ h + 1) :
    (bAnch h j).comp (C (1 / 2) * X) = C ((1 / 2) ^ j) * PZ h (Ico (h + 1 - j) (h + 1)) := by
  unfold bAnch PZ
  rw [Polynomial.prod_comp]
  simp_rw [lin_comp_half, two_mul_xiPole]
  rw [prod_mul_distrib, prod_const, card_range, C_pow,
    prod_reflect_Ico (fun m => X - C ((poleZ h m : ℤ) : ℚ)) hj]

lemma gAB_comp (h i j : ℕ) (hj : j ≤ h + 1) :
    (aAnch h i * bAnch h j).comp (C (1 / 2) * X) =
      C ((1 / 2) ^ (i + j)) * (PZ h (range i) * PZ h (Ico (h + 1 - j) (h + 1))) := by
  rw [mul_comp, aAnch_comp, bAnch_comp h j hj, pow_add, C_mul]; ring

/-! ### Linearity of `A`, `B` -/

lemma Afun_add (h : ℕ) (f g : ℚ[X]) : Afun 2 h (f + g) = Afun 2 h f + Afun 2 h g := by
  unfold Afun cPole
  rw [add_divByMonic, muPoly_add]
  simp only [eval_add, add_div]
  push_cast
  simp only [add_mul, sum_add_distrib]
  ring

lemma Bfun_add (h : ℕ) (f g : ℚ[X]) : Bfun 2 h (f + g) = Bfun 2 h f + Bfun 2 h g := by
  unfold Bfun cPole
  simp only [eval_add, add_div]
  push_cast
  simp only [add_mul, sum_add_distrib]
  ring

lemma Afun_C_mul (h : ℕ) (c : ℚ) (g : ℚ[X]) : Afun 2 h (C c * g) = (c : Q5) * Afun 2 h g := by
  unfold Afun cPole
  rw [← smul_eq_C_mul, smul_divByMonic, muPoly_smul, Algebra.smul_def, eq_ratCast]
  simp only [eval_smul, smul_eq_mul, mul_div_assoc]
  push_cast
  rw [mul_add, mul_sum]
  congr 1
  refine sum_congr rfl (fun m _ => ?_)
  ring

lemma Bfun_C_mul (h : ℕ) (c : ℚ) (g : ℚ[X]) : Bfun 2 h (C c * g) = (c : Q5) * Bfun 2 h g := by
  unfold Bfun cPole
  simp only [eval_mul, eval_C, mul_div_assoc]
  push_cast
  rw [mul_neg, mul_sum]
  congr 1
  refine sum_congr rfl (fun m _ => ?_)
  ring

lemma scale_eq (h i j : ℕ) :
    (2 : Q5) ^ (h + 2) * (((1 / 2 : ℚ) ^ (i + j) : ℚ) : Q5) = (((2 : ℚ) ^ ((h : ℤ) + 2 - i - j) : ℚ) : Q5) := by
  have e : ((h : ℤ) + 2 - i - j) = ((h + 2 : ℕ) : ℤ) - ((i + j : ℕ) : ℤ) := by push_cast; ring
  rw [e, zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast]
  push_cast
  rw [div_pow, one_pow, div_eq_mul_one_div (2 ^ (h + 2) : Q5)]

lemma GA_eq {h i j : ℕ} (hj : j ≤ h + 1) :
    GA h i j = (((2 : ℚ) ^ ((h : ℤ) + 2 - i - j) : ℚ) : Q5) *
      Afun 2 h (PZ h (range i) * PZ h (Ico (h + 1 - j) (h + 1))) := by
  unfold GA
  rw [gAB_comp h i j hj, Afun_C_mul, ← mul_assoc, scale_eq]

lemma GB_eq {h i j : ℕ} (hj : j ≤ h + 1) :
    GB h i j = (((2 : ℚ) ^ ((h : ℤ) + 2 - i - j) : ℚ) : Q5) *
      Bfun 2 h (PZ h (range i) * PZ h (Ico (h + 1 - j) (h + 1))) := by
  unfold GB
  rw [gAB_comp h i j hj, Bfun_C_mul, ← mul_assoc, scale_eq]

/-! ### Case (L): `i + j ≥ K` -/

lemma PZ_L {i j : ℕ} (hi : i ≤ h + 1) (hj : j ≤ h + 1) (hij : h + 1 ≤ i + j) :
    PZ h (range i) * PZ h (Ico (h + 1 - j) (h + 1)) = Dpoly h * PZ h (Ico (h + 1 - j) i) := by
  rw [Dpoly_eq_PZ]
  unfold PZ
  rw [← prod_range_mul_prod_Ico _ (show h + 1 - j ≤ i by omega),
    ← prod_range_mul_prod_Ico _ (show h + 1 - j ≤ h + 1 by omega)]
  ring

lemma Afun_D_mul (h : ℕ) (F : ℚ[X]) : Afun 2 h (Dpoly h * F) = muPoly 2 F := by
  unfold Afun
  rw [mul_divByMonic_cancel_left _ (Dpoly_monic h)]
  rw [sum_eq_zero, add_zero]
  intro m hm
  unfold cPole
  rw [eval_mul, Dpoly_eq_PZ, eval_PZ_eq_zero hm]
  simp

lemma Bfun_D_mul (h : ℕ) (F : ℚ[X]) : Bfun 2 h (Dpoly h * F) = 0 := by
  unfold Bfun
  rw [sum_eq_zero, neg_zero]
  intro m hm
  unfold cPole
  rw [eval_mul, Dpoly_eq_PZ, eval_PZ_eq_zero hm]
  simp

lemma mahlerCoeff_map (q : ℤ[X]) (b : ℕ) :
    mahlerCoeff (q.map (Int.castRingHom ℚ)) b = (mahlerZ q b : ℚ) := by
  unfold mahlerCoeff mahlerZ
  push_cast
  refine sum_congr rfl (fun k _ => ?_)
  have : (2 * (k : ℚ) + 1) = ((2 * (k : ℤ) + 1 : ℤ) : ℚ) := by push_cast; ring
  rw [this, eval_intCast_map]
  simp

/-- `v₂(Δ^b[q(2s+1)](0)) ≥ b + v₂(b!)` for `q ∈ ℤ[X]`. -/
lemma V2_mahlerCoeff_map (q : ℤ[X]) (b : ℕ) :
    V2 ((b : ℤ) + vf b) (mahlerCoeff (q.map (Int.castRingHom ℚ)) b) := by
  rw [mahlerCoeff_map]
  have h1 : (2 : ℤ) ^ (b + vf b) ∣ 2 ^ b * (b ! : ℕ) := by
    rw [pow_add]
    refine mul_dvd_mul_left _ ?_
    unfold vf
    exact_mod_cast (pow_padicValNat_dvd (p := 2) (n := b !))
  have := V2_of_dvd (dvd_trans h1 (dvd_mahlerZ q b))
  push_cast at this
  exact this

/-- `v₂(Lmom p) ≥ −⌊log₂ n⌋ − 3` for `p ∈ ℤ[X]` of degree `< n` (Mahler form). -/
lemma vGe_Lmom_int (q : ℤ[X]) {n : ℕ} (hq : (q.map (Int.castRingHom ℚ)).natDegree < n) :
    vGe 2 (-(Nat.log 2 n : ℤ) - 3) (Lmom 2 (q.map (Int.castRingHom ℚ))) := by
  rw [Lmom_eq_mahler_two]
  refine vGe_sum _ _ (fun b hb => ?_)
  have hb' : b < n := by have := mem_range.mp hb; omega
  have e : (mahlerCoeff (q.map (Int.castRingHom ℚ)) b : Q5) * (zK 2) ^ b / 4 ^ (b + 1) =
      (mahlerCoeff (q.map (Int.castRingHom ℚ)) b : Q5) * (zK 2) ^ (b : ℤ) *
        ((((2 : ℚ) ^ (-2 : ℤ)) ^ (b + 1) : ℚ) : Q5) := by
    rw [zpow_natCast, div_eq_mul_inv]
    congr 1
    push_cast
    rw [← inv_pow]
    norm_num
  rw [e]
  have h1 := vGe_of_V2 (V2_mahlerCoeff_map q b)
  have h2 : vGe 2 0 ((zK 2) ^ (b : ℤ)) := vGe_zK_zpow _
  have h3 := vGe_of_V2 (V2_pow (V2_two_zpow (-2)) (b + 1))
  refine vGe_mono ?_ (vGe_mul (vGe_mul h1 h2) h3)
  have := vf_ge b
  have := log_two_mono hb'.le
  push_cast
  omega

/-- The (L) entries: `G_A = 2^{1−π} Lmom(F′)`, `G_B = 0`. -/
lemma GA_L {i j : ℕ} (hi : i ≤ h + 1) (hj : j ≤ h + 1) (hij : h + 1 ≤ i + j) :
    GA h i j = (((2 : ℚ) ^ ((h : ℤ) + 2 - i - j) : ℚ) : Q5) *
      Lmom 2 ((derivative (PZint h (Ico (h + 1 - j) i))).map (Int.castRingHom ℚ)) := by
  rw [GA_eq hj, PZ_L hi hj hij, Afun_D_mul, muPoly, PZ_eq_map, derivative_map]

lemma GB_L {i j : ℕ} (hi : i ≤ h + 1) (hj : j ≤ h + 1) (hij : h + 1 ≤ i + j) : GB h i j = 0 := by
  rw [GB_eq hj, PZ_L hi hj hij, Bfun_D_mul, mul_zero]

/-! ### Case (U): `i + j ≤ h` -/

lemma PZ_U {i j : ℕ} (hij : i + j ≤ h) :
    PZ h (range i) * PZ h (Ico (h + 1 - j) (h + 1)) = PZ h (range i ∪ Ico (h + 1 - j) (h + 1)) := by
  unfold PZ
  rw [prod_union]
  rw [Finset.disjoint_left]; intro m h1 h2; simp only [mem_range, mem_Ico] at h1 h2; omega

lemma muPoly_zero : muPoly 2 0 = 0 := by simp [muPoly]

lemma divD_U {i j : ℕ} (hij : i + j ≤ h) : PZ h (range i ∪ Ico (h + 1 - j) (h + 1)) /ₘ Dpoly h = 0 := by
  rw [divByMonic_eq_zero_iff (Dpoly_monic h)]
  refine degree_lt_degree ?_
  rw [natDegree_PZ, Dpoly_eq_PZ, natDegree_PZ, card_range, card_union_of_disjoint, card_range, Nat.card_Ico]
  · omega
  · rw [Finset.disjoint_left]; intro m h1 h2; simp only [mem_range, mem_Ico] at h1 h2; omega

lemma prod_range_add_one_q (n : ℕ) : ∏ t ∈ range n, ((t : ℚ) + 1) = ((n ! : ℕ) : ℚ) := by
  rw [← prod_range_add_one_eq_factorial]; push_cast; rfl

lemma prod_range_sub_q (l : ℕ) : ∏ t ∈ range l, ((t : ℚ) - l) = (-1) ^ l * ((l ! : ℕ) : ℚ) := by
  have e1 : (-1 : ℚ) ^ l * ((l ! : ℕ) : ℚ) = ∏ t ∈ range l, (-((t : ℚ) + 1)) := by
    rw [← prod_range_add_one_q, show (-1 : ℚ) ^ l = ∏ t ∈ range l, (-1 : ℚ) by simp, ← prod_mul_distrib]
    exact prod_congr rfl (fun t _ => by ring)
  rw [e1, ← prod_range_reflect (fun t => (t : ℚ) - l) l]
  refine prod_congr rfl (fun t ht => ?_)
  have ht' := mem_range.mp ht
  have e : ((l - 1 - t : ℕ) : ℚ) + t + 1 = l := by
    have : l - 1 - t + t + 1 = l := by omega
    exact_mod_cast this
  linarith

lemma prod_range_sub_q' (l : ℕ) : ∏ t ∈ range l, ((l : ℚ) - t) = ((l ! : ℕ) : ℚ) := by
  have : ∏ t ∈ range l, ((l : ℚ) - t) = ∏ t ∈ range l, ((-1) * ((t : ℚ) - l)) :=
    prod_congr rfl (fun t _ => by ring)
  rw [this, prod_mul_distrib, prod_const, card_range, prod_range_sub_q, ← mul_assoc, ← mul_pow]
  simp

lemma prod_pole_erase (h i N l : ℕ) (hl : l ≤ N) :
    ∏ m ∈ (Ico i (i + N + 1)).erase (i + l), (((poleZ h (i + l) : ℤ) : ℚ) - poleZ h m) =
      2 ^ N * (-1) ^ (N - l) * ((l ! : ℕ) : ℚ) * (((N - l) ! : ℕ) : ℚ) := by
  have hset : (Ico i (i + N + 1)).erase (i + l) = Ico i (i + l) ∪ Ico (i + l + 1) (i + N + 1) := by
    ext m; simp only [mem_erase, mem_Ico, mem_union]; omega
  have hdisj : Disjoint (Ico i (i + l)) (Ico (i + l + 1) (i + N + 1)) := by
    rw [Finset.disjoint_left]; intro m h1 h2; simp only [mem_Ico] at h1 h2; omega
  rw [hset, prod_union hdisj, prod_Ico_eq_prod_range, prod_Ico_eq_prod_range,
    show i + l - i = l by omega, show i + N + 1 - (i + l + 1) = N - l by omega]
  have e1 : ∀ t ∈ range l, (((poleZ h (i + l) : ℤ) : ℚ) - poleZ h (i + t)) = 2 * ((l : ℚ) - t) := by
    intro t _; rw [poleZ_sub]; push_cast; ring
  have e2 : ∀ t ∈ range (N - l), (((poleZ h (i + l) : ℤ) : ℚ) - poleZ h (i + l + 1 + t)) =
      2 * ((-1) * ((t : ℚ) + 1)) := by
    intro t _; rw [poleZ_sub]; push_cast; ring
  rw [prod_congr rfl e1, prod_congr rfl e2, prod_mul_distrib, prod_const, card_range, prod_range_sub_q',
    prod_mul_distrib, prod_const, card_range, prod_mul_distrib, prod_const, card_range, prod_range_add_one_q]
  have hp : (2 : ℚ) ^ N = 2 ^ l * 2 ^ (N - l) := by rw [← pow_add]; congr 1; omega
  rw [hp]; ring

/-- The window of surviving poles. -/
lemma dPrime_U {i j l : ℕ} (hij : i + j ≤ h) (hl : l ≤ h - i - j) :
    dPrime h (i + l) = (PZ h (range i ∪ Ico (h + 1 - j) (h + 1))).eval ((poleZ h (i + l) : ℤ) : ℚ) *
      ∏ m ∈ (Ico i (i + (h - i - j) + 1)).erase (i + l), (((poleZ h (i + l) : ℤ) : ℚ) - poleZ h m) := by
  set Z := range i ∪ Ico (h + 1 - j) (h + 1) with hZ
  set W := Ico i (i + (h - i - j) + 1) with hW
  have hset : range (h + 1) = Z ∪ W := by
    ext m; simp only [hZ, hW, mem_range, mem_union, mem_Ico]; omega
  have hdisj : Disjoint Z W := by
    rw [Finset.disjoint_left]; intro m h1 h2
    simp only [hZ, hW, mem_union, mem_range, mem_Ico] at h1 h2; omega
  have hmW : i + l ∈ W := by simp only [hW, mem_Ico]; omega
  unfold dPrime
  rw [hset, prod_union hdisj, eval_PZ, ← mul_prod_erase W _ hmW, if_pos rfl, one_mul]
  congr 1
  · refine prod_congr rfl (fun m hm => if_neg ?_)
    intro e; subst e
    simp only [hZ, mem_union, mem_range, mem_Ico] at hm; omega
  · exact prod_congr rfl (fun m hm => if_neg (ne_of_mem_erase hm))

lemma cPole_U {i j l : ℕ} (hij : i + j ≤ h) (hl : l ≤ h - i - j) :
    cPole h (PZ h (range i ∪ Ico (h + 1 - j) (h + 1))) (i + l) =
      1 / (2 ^ (h - i - j) * (-1) ^ (h - i - j - l) * ((l ! : ℕ) : ℚ) * (((h - i - j - l) ! : ℕ) : ℚ)) := by
  unfold cPole
  rw [dPrime_U hij hl, prod_pole_erase h i (h - i - j) l hl]
  have hne : (PZ h (range i ∪ Ico (h + 1 - j) (h + 1))).eval ((poleZ h (i + l) : ℤ) : ℚ) ≠ 0 := by
    rw [eval_PZ]
    refine prod_ne_zero_iff.mpr (fun m hm => poleZ_sub_ne_zero ?_)
    intro e; rw [← e] at hm
    simp only [mem_union, mem_range, mem_Ico] at hm; omega
  rw [div_mul_eq_div_div, div_self hne]

lemma cPole_U_zero {i j m : ℕ} (hij : i + j ≤ h) (hm : m ∈ range (h + 1)) (hmW : m ∉ Ico i (h + 1 - j)) :
    cPole h (PZ h (range i ∪ Ico (h + 1 - j) (h + 1))) m = 0 := by
  unfold cPole
  rw [eval_PZ_eq_zero, zero_div]
  simp only [mem_range, mem_Ico, not_and_or, not_le, not_lt] at hm hmW
  simp only [mem_union, mem_range, mem_Ico]; omega

lemma coef_U {N l : ℕ} (hl : l ≤ N) :
    (1 : ℚ) / (2 ^ N * (-1) ^ (N - l) * ((l ! : ℕ) : ℚ) * (((N - l) ! : ℕ) : ℚ)) =
      1 / (2 ^ N * ((N ! : ℕ) : ℚ)) * ((-1) ^ (N - l) * (N.choose l : ℚ)) := by
  have hc : ((N.choose l : ℕ) : ℚ) * ((l ! : ℕ) : ℚ) * (((N - l) ! : ℕ) : ℚ) = ((N ! : ℕ) : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hl
  have h1 : ((l ! : ℕ) : ℚ) ≠ 0 := by positivity
  have h2 : (((N - l) ! : ℕ) : ℚ) ≠ 0 := by positivity
  have hC : ((N.choose l : ℕ) : ℚ) ≠ 0 := by have := Nat.choose_pos hl; positivity
  rw [← hc]
  rcases neg_one_pow_eq_or ℚ (N - l) with hs | hs <;> rw [hs] <;> field_simp

/-- The pole sum in case (U) is a finite difference. -/
lemma sum_U {i j : ℕ} (hij : i + j ≤ h) (Y : ℕ → Q5) :
    ∑ m ∈ range (h + 1), (cPole h (PZ h (range i ∪ Ico (h + 1 - j) (h + 1))) m : Q5) * Y m =
      (((1 : ℚ) / (2 ^ (h - i - j) * (((h - i - j) ! : ℕ) : ℚ)) : ℚ) : Q5) *
        (Δ_[1])^[h - i - j] (fun l => Y (i + l)) 0 := by
  set N := h - i - j with hN
  have hsub : Ico i (h + 1 - j) ⊆ range (h + 1) := fun k hk => by
    simp only [mem_Ico] at hk; simp only [mem_range]; omega
  rw [← sum_subset hsub (fun m hm hmW => by rw [cPole_U_zero hij hm hmW]; simp)]
  rw [sum_Ico_eq_sum_range, show h + 1 - j - i = N + 1 by omega, fwdDiff_iter_eq_sum_shift, mul_sum]
  refine sum_congr rfl (fun l hl => ?_)
  have hl' : l ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hl)
  rw [cPole_U hij hl', coef_U hl']
  simp only [zero_add, smul_eq_mul, mul_one, zsmul_eq_mul]
  push_cast
  ring

/-! ### The (U) entries as finite differences -/

/-- `T(l) = z^{x_{i+l}} P(x_{i+l})`. -/
noncomputable def TseqA (h i l : ℕ) : Q5 := (zK 2) ^ poleZ h (i + l) * Psum 2 (poleZ h (i + l))

/-- `T_B(l) = z^{x_{i+l}}`. -/
noncomputable def TseqB (h i l : ℕ) : Q5 := (zK 2) ^ poleZ h (i + l)

lemma scale_U {i j : ℕ} (hij : i + j ≤ h) :
    (2 : ℚ) ^ ((h : ℤ) + 2 - i - j) * (1 / (2 ^ (h - i - j) * (((h - i - j) ! : ℕ) : ℚ))) =
      4 / (((h - i - j) ! : ℕ) : ℚ) := by
  rw [show ((h : ℤ) + 2 - i - j) = ((h - i - j + 2 : ℕ) : ℤ) by omega, zpow_natCast, pow_add]
  have : (((h - i - j) ! : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp
  norm_num

lemma GA_U {i j : ℕ} (hij : i + j ≤ h) :
    GA h i j = ((4 / (((h - i - j) ! : ℕ) : ℚ) : ℚ) : Q5) * (Δ_[1])^[h - i - j] (TseqA h i) 0 := by
  rw [GA_eq (by omega), PZ_U hij]
  unfold Afun
  rw [divD_U hij, muPoly_zero, zero_add]
  simp_rw [mul_assoc]
  rw [sum_U hij (fun m => (zK 2) ^ poleZ h m * Psum 2 (poleZ h m)), ← mul_assoc, ← Rat.cast_mul, scale_U hij]
  rfl

lemma GB_U {i j : ℕ} (hij : i + j ≤ h) :
    GB h i j = -(((4 / (((h - i - j) ! : ℕ) : ℚ) : ℚ) : Q5) * (Δ_[1])^[h - i - j] (TseqB h i) 0) := by
  rw [GB_eq (by omega), PZ_U hij]
  unfold Bfun
  rw [sum_U hij (fun m => (zK 2) ^ poleZ h m), mul_neg, ← mul_assoc, ← Rat.cast_mul, scale_U hij]
  rfl

/-! ### The recurrences -/

lemma Psum_add_two {x : ℤ} (hx : Even x) : Psum 2 (x + 2) = Psum 2 x - (zK 2) ^ (-x - 1) / ((x + 1 : ℤ) : Q5) ^ 2 := by
  obtain ⟨r, rfl⟩ := hx
  rcases lt_or_ge r 0 with hr | hr
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = -((n : ℤ) + 1) := ⟨(-r - 1).toNat, by omega⟩
    have e1 : (-((n : ℤ) + 1) + -((n : ℤ) + 1) + 2) = -((2 * n : ℕ) : ℤ) := by push_cast; ring
    have e2 : (-((n : ℤ) + 1) + -((n : ℤ) + 1)) = -((2 * (n + 1) : ℕ) : ℤ) := by push_cast; ring
    have e3 : -(-((n : ℤ) + 1) + -((n : ℤ) + 1)) - 1 = ((2 * n + 1 : ℕ) : ℤ) := by push_cast; ring
    have e4 : (((-((n : ℤ) + 1) + -((n : ℤ) + 1) + 1 : ℤ)) : Q5) ^ 2 = ((2 * n + 1 : ℕ) : Q5) ^ 2 := by
      push_cast; ring
    unfold Psum
    rw [e3, e4, e1, e2, if_pos (by omega), if_pos (by omega), Int.natAbs_neg, Int.natAbs_neg,
      Int.natAbs_natCast, Int.natAbs_natCast, show 2 * n / 2 = n by omega, show 2 * (n + 1) / 2 = n + 1 by omega,
      sum_range_succ, zpow_natCast]
    ring
  · lift r to ℕ using hr with n
    have hPx : Psum 2 ((n : ℤ) + n) = -∑ k ∈ range n, ((zK 2) ^ (2 * k + 1))⁻¹ / ((2 * k + 1 : ℕ) : Q5) ^ 2 := by
      unfold Psum
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [if_neg (by omega), show ((n : ℤ) + n) = ((2 * n : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast,
          show 2 * n / 2 = n by omega]
    have e1 : ((n : ℤ) + n + 2) = ((2 * (n + 1) : ℕ) : ℤ) := by push_cast; ring
    have e3 : -((n : ℤ) + n) - 1 = -((2 * n + 1 : ℕ) : ℤ) := by push_cast; ring
    have e4 : ((((n : ℤ) + n + 1 : ℤ)) : Q5) ^ 2 = ((2 * n + 1 : ℕ) : Q5) ^ 2 := by push_cast; ring
    rw [hPx, e3, e4]
    unfold Psum
    rw [e1, if_neg (by omega), Int.natAbs_natCast, show 2 * (n + 1) / 2 = n + 1 by omega, sum_range_succ,
      zpow_neg, zpow_natCast]
    ring

lemma oddS (h i : ℕ) : Odd (poleZ h i + 1) := (even_poleZ h i).add_one

lemma TU_rec (h i l : ℕ) :
    TseqA h i (l + 1) = (zK 2) ^ 2 * TseqA h i l + (-(zK 2)) * ((gSZ (poleZ h i + 1) l : ℚ) : Q5) := by
  unfold TseqA
  set x := poleZ h (i + l) with hx
  have hx2 : poleZ h (i + (l + 1)) = x + 2 := by rw [hx, poleZ_add, poleZ_add]; push_cast; ring
  have hg : ((gSZ (poleZ h i + 1) l : ℚ) : Q5) = 1 / ((x + 1 : ℤ) : Q5) ^ 2 := by
    unfold gSZ; rw [hx, poleZ_add]; push_cast; ring
  rw [hx2, Psum_add_two (even_poleZ h (i + l)), hg]
  have hz1 : (zK 2) ^ (x + 2) = (zK 2) ^ 2 * (zK 2) ^ x := by
    rw [zpow_add₀ zK_ne_zero, mul_comm]; norm_cast
  have hz2 : (zK 2) ^ (x + 2) * (zK 2) ^ (-x - 1) = (zK 2) := by
    rw [← zpow_add₀ zK_ne_zero, show x + 2 + (-x - 1) = 1 by ring, zpow_one]
  rw [mul_sub, mul_div_assoc', hz2, hz1]
  ring

lemma TB_rec (h i l : ℕ) : TseqB h i (l + 1) = (zK 2) ^ 2 * TseqB h i l + 0 * ((gSZ (poleZ h i + 1) l : ℚ) : Q5) := by
  unfold TseqB
  rw [show poleZ h (i + (l + 1)) = poleZ h (i + l) + 2 by rw [poleZ_add, poleZ_add]; push_cast; ring,
    zpow_add₀ zK_ne_zero, zero_mul, add_zero, zpow_two, sq]
  ring

/-! ### Valuations of the ingredients -/

lemma vGe_zK : vGe 2 0 (zK 2) := by simpa using vGe_zK_zpow (p := 2) 1

lemma vGe_four : vGe 2 2 (4 : Q5) := by
  have := vGe_of_V2 (V2_two_zpow 2)
  norm_num at this
  exact this

lemma vGe_zK_sq_sub_one : vGe 2 2 ((zK 2) ^ 2 - 1) := by
  have e : (zK 2) ^ 2 - 1 = -(4 * (zK 2)) := by linear_combination (-1 : Q5) * one_sub_zK_sq (mz := 2)
  rw [e]
  simpa using vGe_neg (vGe_mul vGe_four vGe_zK)

lemma vGe_inv_odd_sq (k : ℕ) : vGe 2 0 ((((2 * k + 1 : ℕ) : Q5) ^ 2)⁻¹) := by
  have e : ((((2 * k + 1 : ℕ) : Q5) ^ 2)⁻¹) = (((1 / ((2 * k + 1 : ℤ) : ℚ)) ^ 2 : ℚ) : Q5) := by
    push_cast; rw [one_div, inv_pow]
  rw [e]
  have := V2_pow (V2_inv_oddInt (n := 2 * k + 1) ⟨k, rfl⟩) 2
  simpa using vGe_of_V2 this

lemma vGe_Psum (x : ℤ) : vGe 2 0 (Psum 2 x) := by
  unfold Psum
  split_ifs
  · refine vGe_sum _ _ (fun k _ => ?_)
    rw [div_eq_mul_inv]
    have := vGe_mul (vGe_zK_zpow (p := 2) ((2 * k + 1 : ℕ) : ℤ)) (vGe_inv_odd_sq k)
    rw [zpow_natCast, add_zero] at this
    exact this
  · refine vGe_neg (vGe_sum _ _ (fun k _ => ?_))
    rw [div_eq_mul_inv, ← zpow_natCast, ← zpow_neg]
    have := vGe_mul (vGe_zK_zpow (p := 2) (-((2 * k + 1 : ℕ) : ℤ))) (vGe_inv_odd_sq k)
    rw [add_zero] at this
    exact this

lemma V2_four_div_factorial (N : ℕ) : V2 (2 - vf N) (4 / ((N ! : ℕ) : ℚ)) := by
  have h4 : V2 2 (4 : ℚ) := by have := V2_two_pow 2; norm_num at this; exact this
  exact V2_div_factorial h4 N

/-- **(U) entries**: `v₂ ≥ N₀ − ⌊log₂ N₀⌋`, `N₀ = h − i − j`. -/
theorem vGe_U {i j : ℕ} (hij : i + j ≤ h) :
    vGe 2 (((h - i - j : ℕ) : ℤ) - Nat.log 2 (h - i - j)) (GA h i j) ∧
      vGe 2 (((h - i - j : ℕ) : ℤ) - Nat.log 2 (h - i - j)) (GB h i j) := by
  set N := h - i - j
  have hc := vGe_of_V2 (V2_four_div_factorial N)
  have hT0 : vGe 2 0 (TseqA h i 0) := by
    have := vGe_mul (vGe_zK_zpow (p := 2) (poleZ h (i + 0))) (vGe_Psum (poleZ h (i + 0)))
    rw [zero_add] at this
    exact this
  have hB0 : vGe 2 0 (TseqB h i 0) := vGe_zK_zpow _
  have hA := vGe_fd_seq vGe_zK_sq_sub_one (vGe_neg vGe_zK) (oddS h i) hT0 (TU_rec h i) N
  have hB := vGe_fd_seq vGe_zK_sq_sub_one (vGe_zero 0) (oddS h i) hB0 (TB_rec h i) N
  refine ⟨?_, ?_⟩
  · rw [GA_U hij]
    refine vGe_mono ?_ (vGe_mul hc hA)
    omega
  · rw [GB_U hij]
    refine vGe_neg (vGe_mono ?_ (vGe_mul hc hB))
    omega

/-- **(U) entries**, `N₀ = 0`: `v₂ ≥ 2`. -/
theorem vGe_U0 {i j : ℕ} (hij : i + j = h) : vGe 2 2 (GA h i j) ∧ vGe 2 2 (GB h i j) := by
  have hN : h - i - j = 0 := by omega
  have h4 : (((4 / (((0 : ℕ) ! : ℕ) : ℚ) : ℚ) : Q5)) = 4 := by norm_num
  have hT0 : vGe 2 0 (TseqA h i 0) := by
    have := vGe_mul (vGe_zK_zpow (p := 2) (poleZ h (i + 0))) (vGe_Psum (poleZ h (i + 0)))
    rw [zero_add] at this
    exact this
  have hB0 : vGe 2 0 (TseqB h i 0) := vGe_zK_zpow _
  refine ⟨?_, ?_⟩
  · rw [GA_U hij.le, hN, h4, Function.iterate_zero, id]
    have := vGe_mul vGe_four hT0
    rwa [add_zero] at this
  · rw [GB_U hij.le, hN, h4, Function.iterate_zero, id]
    have := vGe_neg (vGe_mul vGe_four hB0)
    rwa [add_zero] at this

end Chi2U.TwoAdicAux
