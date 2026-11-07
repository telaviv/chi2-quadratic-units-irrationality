/-
# Lemma 10′ (2-adic bound), part 1: valuations, factorials, finite differences

Adapted from lean_chi2's `Arith/TwoAdicBasis.lean` (χ₂'s Lemma 10); the new points are that the sequences live in
`ℚ(√5)` (valuation `vGe 2`, `Arith/VGe.lean`) and that the shift `s` of `g_s(r) = 1/(s + 2r)²` is an odd *integer*
(the rescaled poles are two-sided).
* `V2 e x` : `v₂(x) ≥ e` for `x ∈ ℚ` (as `‖x‖₂ ≤ 2^{−e}`), closed under `+`, `·`, sums, powers;
* `vf n = v₂(n!)` with `n ≤ v₂(n!) + ⌊log₂ n⌋ + 1` and `v₂(n!) < n` (`n ≥ 1`);
* forward differences on `ℕ → G`: `fd_succ`, `fd_mul_id`, the cast lemma `fd_ratCast`;
* `dCoef n b = Δ^b[x^n](0)`, `b! ∣ dCoef n b`, `dCoef n b = 0` for `n < b`;
* **Mahler coefficients of integer polynomials** (`dvd_mahlerZ`): for `q ∈ ℤ[X]`,
  `2^b b! ∣ Δ^b[q(2s+1)](0)`, so `v₂ ≥ b + v₂(b!)` (used in `TwoAdicEntries.V2_mahlerCoeff_map`);
* `Δ^m [1/(s+2r)²](0) = (−2)^m m! H_m(s)/P_m(s)` for odd `s ∈ ℤ` (`fd_gSZ`), so `v₂ ≥ m + v₂(m!)`;
* `vGe_fd_seq`: if `T(l+1) = Q T(l) + e/(s+2l)²` in `ℚ(√5)` with `v₂(Q − 1) ≥ 2`, `v₂(e), v₂(T(0)) ≥ 0`, then
  `v₂(Δ^m T(0)) ≥ v₂(m!) + m − 2 − ⌊log₂ m⌋` (via the exact recursion `Δ^{m+1}T = (Q−1) Δ^m T + e Δ^m g`).
-/
import Chi2U.Arith.VGe

namespace Chi2U.TwoAdicAux

open Polynomial Finset fwdDiff
open scoped Nat

/-! ### `V2 e x` : `v₂(x) ≥ e` on `ℚ` -/

/-- `v₂(x) ≥ e`, i.e. `‖x‖₂ ≤ 2^{−e}` (true for `x = 0`). -/
def V2 (e : ℤ) (x : ℚ) : Prop := padicNorm 2 x ≤ (2 : ℚ) ^ (-e)

lemma V2_zero (e : ℤ) : V2 e 0 := by unfold V2; rw [padicNorm.zero]; positivity

lemma V2_mono {e e' : ℤ} (h : e' ≤ e) {x : ℚ} (hx : V2 e x) : V2 e' x :=
  hx.trans (zpow_le_zpow_right₀ (by norm_num) (by omega))

lemma V2_add {e : ℤ} {x y : ℚ} (hx : V2 e x) (hy : V2 e y) : V2 e (x + y) :=
  (padicNorm.nonarchimedean (p := 2)).trans (max_le hx hy)

lemma V2_neg {e : ℤ} {x : ℚ} (hx : V2 e x) : V2 e (-x) := by unfold V2 at *; rwa [padicNorm.neg]

lemma V2_sum {ι : Type*} (s : Finset ι) {e : ℤ} (f : ι → ℚ) (h : ∀ i ∈ s, V2 e (f i)) :
    V2 e (∑ i ∈ s, f i) :=
  padicNorm.sum_le' h (by positivity)

lemma V2_mul {e f : ℤ} {x y : ℚ} (hx : V2 e x) (hy : V2 f y) : V2 (e + f) (x * y) := by
  unfold V2 at *
  rw [padicNorm.mul, neg_add, zpow_add₀ two_ne_zero]
  exact mul_le_mul hx hy (padicNorm.nonneg _) (by positivity)

lemma V2_mul' {e f g : ℤ} {x y : ℚ} (hx : V2 e x) (hy : V2 f y) (h : g ≤ e + f) : V2 g (x * y) :=
  V2_mono h (V2_mul hx hy)

lemma V2_one : V2 0 1 := by unfold V2; simp

lemma V2_pow {e : ℤ} {x : ℚ} (hx : V2 e x) (n : ℕ) : V2 (n * e) (x ^ n) := by
  induction n with
  | zero => simpa using V2_one
  | succ n ih =>
    rw [pow_succ]
    have := V2_mul ih hx
    convert this using 1
    push_cast; ring

lemma V2_of_dvd {k : ℕ} {z : ℤ} (h : (2 : ℤ) ^ k ∣ z) : V2 k (z : ℚ) := by
  unfold V2
  have := (padicNorm.dvd_iff_norm_le (p := 2) (n := k) (z := z)).mp (by exact_mod_cast h)
  simpa using this

lemma V2_two_pow (n : ℕ) : V2 n ((2 : ℚ) ^ n) := by
  have := V2_of_dvd (k := n) (z := 2 ^ n) dvd_rfl
  simpa using this

lemma V2_div_of_norm {e k : ℤ} {x y : ℚ} (hx : V2 e x) (hy : padicNorm 2 y = (2 : ℚ) ^ (-k)) :
    V2 (e - k) (x / y) := by
  unfold V2 at *
  rw [padicNorm.div, hy, div_le_iff₀ (by positivity), ← zpow_add₀ two_ne_zero]
  convert hx using 2; ring

lemma padicNorm_two_oddInt {n : ℤ} (hn : Odd n) : padicNorm 2 (n : ℚ) = 1 := by
  refine (padicNorm.int_eq_one_iff n).mpr ?_
  rintro ⟨c, hc⟩
  obtain ⟨k, rfl⟩ := hn
  omega

lemma V2_div_oddInt {e : ℤ} {x : ℚ} (hx : V2 e x) {n : ℤ} (hn : Odd n) : V2 e (x / n) := by
  have := V2_div_of_norm (k := 0) hx (by rw [padicNorm_two_oddInt hn]; simp)
  simpa using this

lemma V2_inv_oddInt {n : ℤ} (hn : Odd n) : V2 0 (1 / (n : ℚ)) := V2_div_oddInt V2_one hn

lemma V2_two_zpow (n : ℤ) : V2 n ((2 : ℚ) ^ n) := by
  unfold V2
  have h := padicNorm_p_zpow (p := 2) n
  push_cast at h
  rw [h]

/-- From `V2` on `ℚ` to `vGe 2` on `ℚ(√5)`. -/
lemma vGe_of_V2 {e : ℤ} {x : ℚ} (hx : V2 e x) : vGe 2 e (x : Q5) := by
  apply vGe_ratCast_of_padicNorm; unfold V2 at hx; exact_mod_cast hx

/-! ### `v₂(n!)` -/

/-- `v₂(n!)`. -/
def vf (n : ℕ) : ℕ := padicValNat 2 n !

lemma vf_le (n : ℕ) : vf n ≤ n := by unfold vf; exact padicValNat_factorial_le 2 n

lemma vf_lt {n : ℕ} (hn : n ≠ 0) : vf n < n := by unfold vf; exact padicValNat_factorial_lt_of_ne_zero 2 hn

lemma vf_ge (n : ℕ) : n ≤ vf n + Nat.log 2 n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp [vf]
    · have e1 : vf n = vf (n / 2) + n / 2 := by
        unfold vf
        rw [← padicValNat_mul_div_factorial (p := 2) n, padicValNat_factorial_mul]
      have e2 := Nat.log_div_base 2 n
      have e3 : 0 < Nat.log 2 n := Nat.log_pos (by norm_num) h
      have := ih (n / 2) (by omega)
      omega

lemma padicNorm_factorial (n : ℕ) : padicNorm 2 ((n ! : ℕ) : ℚ) = (2 : ℚ) ^ (-((vf n : ℕ) : ℤ)) := by
  unfold vf
  rw [padicNorm.eq_zpow_of_nonzero (by positivity), padicValRat.of_nat]
  norm_num

lemma V2_div_factorial {e : ℤ} {x : ℚ} (hx : V2 e x) (n : ℕ) : V2 (e - vf n) (x / (n ! : ℕ)) :=
  V2_div_of_norm hx (padicNorm_factorial n)

lemma log_two_mono {a b : ℕ} (h : a ≤ b) : Nat.log 2 a ≤ Nat.log 2 b := Nat.log_mono_right h

/-! ### Forward differences on `ℕ → G` -/

lemma fd_succ {G : Type*} [AddCommGroup G] (f : ℕ → G) (b y : ℕ) :
    (Δ_[1])^[b + 1] f y = (Δ_[1])^[b] f (y + 1) - (Δ_[1])^[b] f y := by
  rw [Function.iterate_succ_apply']; rfl

lemma fd_shift (f : ℕ → ℚ) (b y m : ℕ) :
    (Δ_[1])^[b] f (y + m) = (Δ_[1])^[b] (fun r => f (r + m)) y :=
  (fwdDiff_iter_comp_add 1 f m b y).symm

lemma fd_mul_id (f : ℕ → ℚ) (b y : ℕ) :
    (Δ_[1])^[b + 1] (fun x : ℕ => (x : ℚ) * f x) y =
      y * (Δ_[1])^[b + 1] f y + (b + 1) * (Δ_[1])^[b] f (y + 1) := by
  induction b generalizing y with
  | zero =>
    simp only [zero_add, Function.iterate_one, Function.iterate_zero, id_eq, fwdDiff, Nat.cast_zero]
    push_cast; ring
  | succ b ih =>
    have h1 := fd_succ f (b + 1) y
    have h2 := fd_succ f b (y + 1)
    rw [fd_succ _ (b + 1) y, ih, ih]
    push_cast
    linear_combination (-(y : ℚ)) * h1 - ((b : ℚ) + 1) * h2

/-- Forward differences commute with the cast `ℚ → ℚ(√5)`. -/
lemma fd_ratCast (f : ℕ → ℚ) (k y : ℕ) :
    (Δ_[1])^[k] (fun l => ((f l : ℚ) : Q5)) y = (((Δ_[1])^[k] f y : ℚ) : Q5) := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih => rw [fd_succ, fd_succ, ih, ih]; push_cast; rfl

/-! ### `dCoef n b = Δ^b[x^n](0)`, `b! ∣ dCoef n b` -/

/-- Newton coefficients `Δ^b[x^n](0)` (integers). -/
def dCoef (n b : ℕ) : ℤ := ∑ k ∈ range (b + 1), (-1 : ℤ) ^ (b - k) * (b.choose k : ℤ) * (k : ℤ) ^ n

lemma dCoef_eq_fd (n b : ℕ) : (dCoef n b : ℚ) = (Δ_[1])^[b] (fun x : ℕ => (x : ℚ) ^ n) 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  unfold dCoef
  push_cast
  refine sum_congr rfl (fun k _ => ?_)
  rw [zsmul_eq_mul]
  push_cast
  simp

lemma dCoef_eq_zero {n b : ℕ} (h : n < b) : dCoef n b = 0 := by
  have := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℚ) (n := b) h) 0
  have e : (dCoef n b : ℚ) = (Δ_[1])^[b] (fun x : ℚ => x ^ n) 0 := by
    rw [fwdDiff_iter_eq_sum_shift]
    unfold dCoef
    push_cast
    refine sum_congr rfl (fun k _ => ?_)
    rw [zsmul_eq_mul]
    push_cast
    simp
  rw [Pi.zero_apply, ← e] at this
  exact_mod_cast this

lemma dCoef_succ (n b : ℕ) : dCoef (n + 1) (b + 1) = (b + 1) * (dCoef n b + dCoef n (b + 1)) := by
  have h := fd_mul_id (fun x : ℕ => (x : ℚ) ^ n) b 0
  have e : (fun x : ℕ => (x : ℚ) ^ (n + 1)) = fun x : ℕ => (x : ℚ) * (x : ℚ) ^ n := by funext x; ring
  have key : (dCoef (n + 1) (b + 1) : ℚ) = (b + 1) * (dCoef n b + dCoef n (b + 1)) := by
    rw [dCoef_eq_fd, dCoef_eq_fd, dCoef_eq_fd, e, h, fd_succ _ b 0]
    simp
  exact_mod_cast key

lemma factorial_dvd_dCoef (n b : ℕ) : ((b ! : ℕ) : ℤ) ∣ dCoef n b := by
  induction n generalizing b with
  | zero =>
    cases b with
    | zero => simp
    | succ b => rw [dCoef_eq_zero (by omega)]; exact dvd_zero _
  | succ n ih =>
    cases b with
    | zero => simp
    | succ b =>
      rw [dCoef_succ, Nat.factorial_succ]
      push_cast
      refine mul_dvd_mul_left _ (dvd_add (ih b) (dvd_trans ?_ (ih (b + 1))))
      exact_mod_cast Nat.factorial_dvd_factorial (Nat.le_succ b)

/-! ### Mahler coefficients of integer polynomials -/

/-- `Δ^b[q(2s+1)](0)` for `q ∈ ℤ[X]`. -/
def mahlerZ (q : ℤ[X]) (b : ℕ) : ℤ :=
  ∑ k ∈ range (b + 1), (-1 : ℤ) ^ (b - k) * (b.choose k : ℤ) * q.eval (2 * (k : ℤ) + 1)

lemma mahlerZ_add (p q : ℤ[X]) (b : ℕ) : mahlerZ (p + q) b = mahlerZ p b + mahlerZ q b := by
  unfold mahlerZ; rw [← sum_add_distrib]; refine sum_congr rfl (fun k _ => ?_); rw [eval_add]; ring

lemma mahlerZ_monomial (n : ℕ) (c : ℤ) (b : ℕ) :
    mahlerZ (monomial n c) b = c * ∑ r ∈ range (n + 1), (n.choose r : ℤ) * 2 ^ r * dCoef r b := by
  unfold mahlerZ dCoef
  simp only [eval_monomial]
  have e : ∀ k : ℕ, (2 * (k : ℤ) + 1) ^ n = ∑ r ∈ range (n + 1), (2 * (k : ℤ)) ^ r * (n.choose r : ℤ) := by
    intro k; rw [add_pow]; simp
  simp only [e, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun r _ => sum_congr rfl (fun k _ => ?_))
  rw [mul_pow]; ring

/-- `2^b b! ∣ Δ^b[q(2s+1)](0)` for `q ∈ ℤ[X]`. -/
lemma dvd_mahlerZ (q : ℤ[X]) (b : ℕ) : (2 ^ b * (b ! : ℕ) : ℤ) ∣ mahlerZ q b := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [mahlerZ_add]; exact dvd_add hp hq
  | monomial n c =>
    rw [mahlerZ_monomial]
    refine dvd_mul_of_dvd_right (dvd_sum (fun r _ => ?_)) _
    rcases Nat.lt_or_ge r b with hr | hr
    · rw [dCoef_eq_zero hr, mul_zero]; exact dvd_zero _
    · rw [mul_assoc]
      refine dvd_mul_of_dvd_right (mul_dvd_mul ?_ (factorial_dvd_dCoef r b)) _
      exact pow_dvd_pow 2 hr

/-! ### `g_s(r) = 1/(s + 2r)²`, `s` an odd integer -/

/-- `g_s(r) = 1/(s + 2r)²`. -/
def gSZ (s : ℤ) (r : ℕ) : ℚ := 1 / ((s : ℚ) + 2 * r) ^ 2

/-- `P_m(s) = ∏_{a≤m} (s + 2a)`. -/
def PSZ (s : ℤ) (m : ℕ) : ℚ := ∏ a ∈ range (m + 1), ((s : ℚ) + 2 * a)

/-- `H_m(s) = ∑_{a≤m} 1/(s + 2a)`. -/
def HSZ (s : ℤ) (m : ℕ) : ℚ := ∑ a ∈ range (m + 1), 1 / ((s : ℚ) + 2 * a)

lemma oddInt_add_two_mul {s : ℤ} (hs : Odd s) (a : ℕ) : Odd (s + 2 * (a : ℤ)) := hs.add_even (even_two_mul _)

lemma cast_add_two_mul (s : ℤ) (a : ℕ) : (s : ℚ) + 2 * (a : ℚ) = ((s + 2 * (a : ℤ) : ℤ) : ℚ) := by push_cast; ring

lemma add_two_mul_ne_zero {s : ℤ} (hs : Odd s) (a : ℕ) : (s : ℚ) + 2 * (a : ℚ) ≠ 0 := by
  rw [cast_add_two_mul]
  obtain ⟨k, hk⟩ := oddInt_add_two_mul hs a
  intro h
  have : s + 2 * (a : ℤ) = 0 := by exact_mod_cast h
  omega

lemma PSZ_ne_zero {s : ℤ} (hs : Odd s) (m : ℕ) : PSZ s m ≠ 0 :=
  prod_ne_zero_iff.mpr (fun a _ => add_two_mul_ne_zero hs a)

lemma fd_gSZ (m : ℕ) : ∀ s : ℤ, Odd s →
    (Δ_[1])^[m] (gSZ s) 0 = (-2) ^ m * (m ! : ℕ) * HSZ s m / PSZ s m := by
  induction m with
  | zero =>
    intro s hs
    have : (s : ℚ) ≠ 0 := by simpa using add_two_mul_ne_zero hs 0
    simp [gSZ, HSZ, PSZ]
    field_simp
  | succ m ih =>
    intro s hs
    have hs0 : (s : ℚ) ≠ 0 := by simpa using add_two_mul_ne_zero hs 0
    have hs1 : (s : ℚ) + 2 * ((m : ℚ) + 1) ≠ 0 := by simpa using add_two_mul_ne_zero hs (m + 1)
    have hP : PSZ s (m + 1) ≠ 0 := PSZ_ne_zero hs _
    have hshift : (fun r => gSZ s (r + 1)) = gSZ (s + 2) := by
      funext r; unfold gSZ; push_cast; ring_nf
    have hP1 : PSZ (s + 2) m = PSZ s (m + 1) / s := by
      rw [eq_div_iff hs0]
      unfold PSZ
      rw [prod_range_succ' (fun a => (s : ℚ) + 2 * a)]
      push_cast
      simp only [mul_zero, add_zero]
      congr 1
      refine prod_congr rfl (fun a _ => by ring)
    have hP2 : PSZ s m = PSZ s (m + 1) / ((s : ℚ) + 2 * ((m : ℚ) + 1)) := by
      rw [eq_div_iff hs1]
      unfold PSZ
      rw [prod_range_succ _ (m + 1)]
      push_cast; ring
    have hH1 : HSZ (s + 2) m = HSZ s (m + 1) - 1 / s := by
      unfold HSZ
      rw [sum_range_succ' (fun a => 1 / ((s : ℚ) + 2 * a))]
      push_cast
      simp only [mul_zero, add_zero, add_sub_cancel_right]
      refine sum_congr rfl (fun a _ => by ring_nf)
    have hH2 : HSZ s m = HSZ s (m + 1) - 1 / ((s : ℚ) + 2 * ((m : ℚ) + 1)) := by
      unfold HSZ
      rw [sum_range_succ _ (m + 1)]
      push_cast; ring
    rw [fd_succ, zero_add, fd_shift _ _ 0 1, hshift, ih (s + 2) (hs.add_even even_two), ih s hs,
      hP1, hP2, hH1, hH2, Nat.factorial_succ]
    push_cast
    field_simp
    ring

lemma padicNorm_PSZ {s : ℤ} (hs : Odd s) (m : ℕ) : padicNorm 2 (PSZ s m) = 1 := by
  unfold PSZ
  induction m with
  | zero => simpa using padicNorm_two_oddInt hs
  | succ m ih =>
    rw [prod_range_succ, padicNorm.mul, ih, one_mul, cast_add_two_mul]
    exact padicNorm_two_oddInt (oddInt_add_two_mul hs _)

lemma V2_HSZ {s : ℤ} (hs : Odd s) (m : ℕ) : V2 0 (HSZ s m) := by
  unfold HSZ
  refine V2_sum _ _ (fun a _ => ?_)
  rw [cast_add_two_mul]
  exact V2_inv_oddInt (oddInt_add_two_mul hs a)

lemma V2_gSZ {s : ℤ} (hs : Odd s) (r : ℕ) : V2 0 (gSZ s r) := by
  unfold gSZ
  rw [cast_add_two_mul, ← one_div_pow]
  simpa using V2_pow (V2_inv_oddInt (oddInt_add_two_mul hs r)) 2

lemma V2_fd_gSZ {s : ℤ} (hs : Odd s) (m : ℕ) : V2 ((m : ℤ) + vf m) ((Δ_[1])^[m] (gSZ s) 0) := by
  rw [fd_gSZ m s hs]
  have h1 : V2 m ((-2 : ℚ) ^ m) := by
    have := V2_pow (V2_neg (V2_two_pow 1)) m
    simpa using this
  have h2 : V2 (vf m) (((m ! : ℕ) : ℤ) : ℚ) := by
    refine V2_of_dvd ?_
    unfold vf
    exact_mod_cast (pow_padicValNat_dvd (p := 2) (n := m !))
  push_cast at h2
  have := V2_div_of_norm (k := 0) (y := PSZ s m) (V2_mul (V2_mul h1 h2) (V2_HSZ hs m))
    (by rw [padicNorm_PSZ hs]; simp)
  simpa using this

/-! ### The sequence bound in `ℚ(√5)` -/

lemma fd_seq_formula {R : Type*} [CommRing R] {Q e : R} {T g : ℕ → R}
    (hrec : ∀ l, T (l + 1) = Q * T l + e * g l) (m y : ℕ) :
    (Δ_[1])^[m] T y = (Q - 1) ^ m * T y +
      e * ∑ k ∈ range m, (Q - 1) ^ (m - 1 - k) * (Δ_[1])^[k] g y := by
  induction m generalizing y with
  | zero => simp
  | succ m ih =>
    rw [fd_succ, ih, ih, hrec, sum_range_succ']
    simp only [Function.iterate_zero, id, Nat.sub_zero]
    rw [show m + 1 - 1 = m by omega]
    have hs : ∑ k ∈ range m, (Q - 1) ^ (m - 1 - k) * (Δ_[1])^[k] g (y + 1) -
        ∑ k ∈ range m, (Q - 1) ^ (m - 1 - k) * (Δ_[1])^[k] g y =
        ∑ k ∈ range m, (Q - 1) ^ (m - (k + 1)) * (Δ_[1])^[k + 1] g y := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl (fun k _ => ?_)
      rw [fd_succ, show m - (k + 1) = m - 1 - k by omega]
      ring
    linear_combination e * hs

/-- **The sequence bound.** If `T(l+1) = Q T(l) + e/(s+2l)²` with `v₂(Q − 1) ≥ 2`, `v₂(e) ≥ 0`, `v₂(T 0) ≥ 0`, then
`v₂(Δ^m T(0)) ≥ v₂(m!) + m − 2 − ⌊log₂ m⌋`. -/
theorem vGe_fd_seq {Q e : Q5} (hη : vGe 2 2 (Q - 1)) (he : vGe 2 0 e) {s : ℤ} (hs : Odd s) {T : ℕ → Q5}
    (hT0 : vGe 2 0 (T 0)) (hrec : ∀ l, T (l + 1) = Q * T l + e * ((gSZ s l : ℚ) : Q5)) (m : ℕ) :
    vGe 2 ((vf m : ℤ) + m - 2 - Nat.log 2 m) ((Δ_[1])^[m] T 0) := by
  rw [fd_seq_formula hrec]
  refine vGe_add (vGe_mono ?_ (vGe_mul (vGe_pow hη m) hT0)) ?_
  · have := vf_le m; omega
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [range_zero, sum_empty, mul_zero]; exact vGe_zero _
    refine vGe_mono ?_ (vGe_mul he (vGe_sum (n := (vf m : ℤ) + m - 2 - Nat.log 2 m) _ _ (fun k hk => ?_)))
    · simp
    have hk := mem_range.mp hk
    rw [fd_ratCast]
    refine vGe_mono ?_ (vGe_mul (vGe_pow hη _) (vGe_of_V2 (V2_fd_gSZ hs k)))
    have h1 := vf_ge k
    have h2 := vf_lt (Nat.pos_iff_ne_zero.mp hm)
    have h3 := log_two_mono hk.le
    omega

end Chi2U.TwoAdicAux
