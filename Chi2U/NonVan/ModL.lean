/-
# Reduction modulo a prime above `ℓ` in `O_ℓ ⊂ ℚ(√d)` (infrastructure for Lemma P′, any `az`)

For `az ≥ 1` (`d = (az/2)² + 1`) and a prime `ℓ`:
* `Rl az ℓ`: the subring `O_ℓ = {x : pInt ℓ x}` of `ℚ(√d)` (`ℤ_(ℓ)[φ]` for `az = 4`);
* `mI az ℓ`: a maximal ideal of `Rl az ℓ` containing `ℓ` (exists since `1 ∉ ℓ·Rl`; this is PROOF_U's prime `𝔩 | ℓ`);
* `Fl az ℓ := Rl az ℓ ⧸ mI az ℓ`, a field of characteristic `ℓ`, and `red az ℓ : Rl az ℓ →+* Fl az ℓ`;
* `Cong ℓ x a`: `x ∈ O_ℓ` and `red x = a`. Congruences mod `ℓ` (`vGe ℓ 1 (x − y)`) are respected
  (`Cong_of_vGe_sub`), and conversely `Cong x a`, `a ≠ 0` gives `¬ vGe ℓ 1 x` (`not_vGe_of_Cong`).
Only the direction "`x ≡ 0 mod ℓ` ⇒ `red x = 0`" is used, which is why any maximal ideal over `ℓ` will do.
-/
import Chi2U.Mahler

namespace Chi2U
namespace LP

open Polynomial Finset

variable (az : ℕ) [Fact (1 ≤ az)] (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

/-- `O_ℓ` (`pInt`; `ℤ_(ℓ)[φ]` for `az = 4`) as a subring of `ℚ(√d)`. -/
def Rl : Subring (Qd az) where
  carrier := {x | pInt ℓ x}
  mul_mem' := pInt_mul
  one_mem' := pInt_one
  add_mem' := pInt_add
  zero_mem' := pInt_zero
  neg_mem' := pInt_neg

variable {az ℓ} in
lemma mem_Rl {x : Qd az} : x ∈ Rl az ℓ ↔ pInt ℓ x := Iff.rfl

/-- The ideal `ℓ · O_ℓ`. -/
def Il : Ideal (Rl az ℓ) := Ideal.span {(ℓ : Rl az ℓ)}

lemma vGe_ell : vGe ℓ 1 (ℓ : Qd az) := by
  have := vGe_ratCast (az := az) (p := ℓ) (ℓ : ℚ)
  rw [padicValRat.self hℓ.out.one_lt] at this
  simpa using this

variable {az ℓ} in
lemma mem_Il_iff {x : Rl az ℓ} : x ∈ Il az ℓ ↔ vGe ℓ 1 (x : Qd az) := by
  rw [Il, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    have := vGe_mul (vGe_ell az ℓ) (vGe_of_pInt c.2)
    simpa using this
  · intro hx
    refine ⟨⟨((ℓ : ℚ) ^ (-1 : ℤ)) • (x : Qd az), (vGe_iff_pInt 1 _).mp hx⟩, ?_⟩
    apply Subtype.ext
    have hp0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.out.ne_zero
    simp only [Subring.coe_mul, Subring.coe_natCast]
    rw [Algebra.smul_def, ← mul_assoc]
    have : (ℓ : Qd az) * algebraMap ℚ (Qd az) ((ℓ : ℚ) ^ (-1 : ℤ)) = 1 := by
      rw [show (ℓ : Qd az) = algebraMap ℚ (Qd az) (ℓ : ℚ) by simp, ← map_mul, zpow_neg_one, mul_inv_cancel₀ hp0,
        map_one]
    rw [this, one_mul]

lemma not_vGe_one : ¬ vGe ℓ 1 (1 : Qd az) := by
  intro h
  have := padicNorm_le_of_vGe (az := az) (p := ℓ) (r := 1) (by simpa using h)
  rw [padicNorm.one] at this
  have h1 : (1 : ℚ) < ℓ := by exact_mod_cast hℓ.out.one_lt
  have : (ℓ : ℚ) ^ (-1 : ℤ) < 1 := by
    rw [zpow_neg_one]; exact inv_lt_one_of_one_lt₀ h1
  linarith

lemma Il_ne_top : Il az ℓ ≠ ⊤ := by
  intro h
  have h1 : (1 : Rl az ℓ) ∈ Il az ℓ := (Ideal.eq_top_iff_one _).mp h
  have h2 : vGe ℓ 1 ((1 : Rl az ℓ) : Qd az) := mem_Il_iff.mp h1
  rw [OneMemClass.coe_one] at h2
  exact not_vGe_one az ℓ h2

/-- A maximal ideal of `O_ℓ` above `ℓ`. -/
noncomputable def mI : Ideal (Rl az ℓ) := Classical.choose (Ideal.exists_le_maximal _ (Il_ne_top az ℓ))

instance mI_isMaximal : (mI az ℓ).IsMaximal := (Classical.choose_spec (Ideal.exists_le_maximal _ (Il_ne_top az ℓ))).1

lemma Il_le_mI : Il az ℓ ≤ mI az ℓ := (Classical.choose_spec (Ideal.exists_le_maximal _ (Il_ne_top az ℓ))).2

/-- The residue field. -/
abbrev Fl : Type := Rl az ℓ ⧸ mI az ℓ

noncomputable instance : Field (Fl az ℓ) := Ideal.Quotient.field (mI az ℓ)

/-- Reduction. -/
noncomputable def red : Rl az ℓ →+* Fl az ℓ := Ideal.Quotient.mk (mI az ℓ)

variable {az ℓ} in
lemma red_eq_zero_of_vGe {x : Rl az ℓ} (hx : vGe ℓ 1 (x : Qd az)) : red az ℓ x = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Il_le_mI az ℓ (mem_Il_iff.mpr hx))

lemma red_natCast_ell : ((ℓ : ℕ) : Fl az ℓ) = 0 := by
  rw [← map_natCast (red az ℓ)]
  exact red_eq_zero_of_vGe (by simpa using vGe_ell az ℓ)

instance charP_Fl : CharP (Fl az ℓ) ℓ := (CharP.charP_iff_prime_eq_zero hℓ.out).mpr (red_natCast_ell az ℓ)

/-! ### `Cong` -/

variable {az} in
/-- `x ∈ O_ℓ` with reduction `a`. -/
def Cong (x : Qd az) (a : Fl az ℓ) : Prop := ∃ h : x ∈ Rl az ℓ, red az ℓ ⟨x, h⟩ = a

variable {az ℓ}

lemma Cong.mem {x : Qd az} {a : Fl az ℓ} (h : Cong ℓ x a) : pInt ℓ x := h.1

lemma Cong.unique {x : Qd az} {a b : Fl az ℓ} (ha : Cong ℓ x a) (hb : Cong ℓ x b) : a = b := by
  obtain ⟨h1, rfl⟩ := ha; obtain ⟨h2, rfl⟩ := hb; rfl

lemma Cong_red (x : Rl az ℓ) : Cong ℓ (x : Qd az) (red az ℓ x) := ⟨x.2, rfl⟩

lemma Cong_add {x y : Qd az} {a b : Fl az ℓ} (hx : Cong ℓ x a) (hy : Cong ℓ y b) : Cong ℓ (x + y) (a + b) := by
  obtain ⟨h1, rfl⟩ := hx; obtain ⟨h2, rfl⟩ := hy
  exact ⟨(Rl az ℓ).add_mem h1 h2, by rw [← map_add]; rfl⟩

lemma Cong_mul {x y : Qd az} {a b : Fl az ℓ} (hx : Cong ℓ x a) (hy : Cong ℓ y b) : Cong ℓ (x * y) (a * b) := by
  obtain ⟨h1, rfl⟩ := hx; obtain ⟨h2, rfl⟩ := hy
  exact ⟨(Rl az ℓ).mul_mem h1 h2, by rw [← map_mul]; rfl⟩

lemma Cong_neg {x : Qd az} {a : Fl az ℓ} (hx : Cong ℓ x a) : Cong ℓ (-x) (-a) := by
  obtain ⟨h1, rfl⟩ := hx
  exact ⟨(Rl az ℓ).neg_mem h1, by rw [← map_neg]; rfl⟩

lemma Cong_sub {x y : Qd az} {a b : Fl az ℓ} (hx : Cong ℓ x a) (hy : Cong ℓ y b) : Cong ℓ (x - y) (a - b) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact Cong_add hx (Cong_neg hy)

lemma Cong_one : Cong ℓ (1 : Qd az) 1 := ⟨(Rl az ℓ).one_mem, by rw [← map_one (red az ℓ)]; rfl⟩

lemma Cong_zero : Cong ℓ (0 : Qd az) 0 := ⟨(Rl az ℓ).zero_mem, by rw [← map_zero (red az ℓ)]; rfl⟩

lemma Cong_pow {x : Qd az} {a : Fl az ℓ} (hx : Cong ℓ x a) (n : ℕ) : Cong ℓ (x ^ n) (a ^ n) := by
  induction n with
  | zero => simpa using Cong_one
  | succ n ih => rw [pow_succ, pow_succ]; exact Cong_mul ih hx

lemma Cong_sum {ι : Type*} (s : Finset ι) (f : ι → Qd az) (g : ι → Fl az ℓ) (h : ∀ i ∈ s, Cong ℓ (f i) (g i)) :
    Cong ℓ (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Cong_zero
  | insert a s ha ih =>
      rw [sum_insert ha, sum_insert ha]
      exact Cong_add (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

lemma Cong_prod {ι : Type*} (s : Finset ι) (f : ι → Qd az) (g : ι → Fl az ℓ) (h : ∀ i ∈ s, Cong ℓ (f i) (g i)) :
    Cong ℓ (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Cong_one
  | insert a s ha ih =>
      rw [prod_insert ha, prod_insert ha]
      exact Cong_mul (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

lemma Cong_intCast (n : ℤ) : Cong ℓ (n : Qd az) (n : Fl az ℓ) :=
  ⟨intCast_mem (Rl az ℓ) n, by rw [← map_intCast (red az ℓ)]; rfl⟩

lemma Cong_natCast (n : ℕ) : Cong ℓ (n : Qd az) (n : Fl az ℓ) := by
  simpa using Cong_intCast (ℓ := ℓ) (n : ℤ)

lemma Cong_ofNat (n : ℕ) [n.AtLeastTwo] : Cong ℓ (OfNat.ofNat n : Qd az) (OfNat.ofNat n : Fl az ℓ) :=
  Cong_natCast n

lemma Cong_zero_of_vGe {x : Qd az} (hx : vGe ℓ 1 x) : Cong ℓ x 0 :=
  ⟨pInt_of_vGe (vGe_mono (by norm_num) hx), red_eq_zero_of_vGe hx⟩

lemma Cong_of_vGe_sub {x y : Qd az} {a : Fl az ℓ} (hy : Cong ℓ y a) (hxy : vGe ℓ 1 (x - y)) : Cong ℓ x a := by
  have := Cong_add (Cong_zero_of_vGe hxy) hy
  simpa using this

lemma Cong_congr {x y : Qd az} {a b : Fl az ℓ} (h : Cong ℓ x a) (hxy : x = y) (hab : a = b) : Cong ℓ y b := by
  subst hxy hab; exact h

lemma eq_zero_of_Cong_of_vGe {x : Qd az} {a : Fl az ℓ} (h : Cong ℓ x a) (hx : vGe ℓ 1 x) : a = 0 :=
  h.unique (Cong_zero_of_vGe hx)

lemma not_vGe_of_Cong {x : Qd az} {a : Fl az ℓ} (h : Cong ℓ x a) (ha : a ≠ 0) : ¬ vGe ℓ 1 x :=
  fun hx => ha (eq_zero_of_Cong_of_vGe h hx)

lemma Cong_inv {x : Qd az} {a : Fl az ℓ} (hx : Cong ℓ x a) (ha : a ≠ 0) (hxi : pInt ℓ x⁻¹) : Cong ℓ x⁻¹ a⁻¹ := by
  have hx0 : x ≠ 0 := by
    rintro rfl; exact ha (hx.unique Cong_zero)
  obtain ⟨b, hb⟩ : ∃ b, Cong ℓ x⁻¹ b := ⟨_, Cong_red ⟨x⁻¹, hxi⟩⟩
  have h1 := Cong_mul hx hb
  rw [mul_inv_cancel₀ hx0] at h1
  have h2 : a * b = 1 := h1.unique Cong_one
  rwa [inv_eq_of_mul_eq_one_right h2]

/-- A rational with nonzero reduction is an `ℓ`-unit. -/
lemma padicNorm_eq_one_of_Cong {r : ℚ} {a : Fl az ℓ} (h : Cong ℓ (r : Qd az) a) (ha : a ≠ 0) : padicNorm ℓ r = 1 := by
  have h1 : padicNorm ℓ r ≤ 1 := by
    have := padicNorm_le_of_vGe (p := ℓ) (n := 0) (vGe_of_pInt h.mem); simpa using this
  have h2 : ¬ padicNorm ℓ r ≤ (ℓ : ℚ) ^ (-(1 : ℤ)) := fun hr =>
    not_vGe_of_Cong h ha (vGe_ratCast_of_padicNorm hr)
  have hr0 : r ≠ 0 := by rintro rfl; exact h2 (by rw [padicNorm.zero]; positivity)
  rw [padicNorm.eq_zpow_of_nonzero hr0] at h1 h2 ⊢
  have hl : (1 : ℚ) < ℓ := by exact_mod_cast hℓ.out.one_lt
  have e1 : -padicValRat ℓ r ≤ 0 := by
    by_contra hc
    have : (1 : ℚ) < (ℓ : ℚ) ^ (-padicValRat ℓ r) := one_lt_zpow₀ hl (by omega)
    linarith
  have e2 : ¬ (-padicValRat ℓ r ≤ -1) := fun hc => h2 (zpow_le_zpow_right₀ hl.le hc)
  have : -padicValRat ℓ r = 0 := by omega
  rw [this, zpow_zero]

/-! ### The unit `z` -/

variable (az ℓ) in
/-- `z` reduced. -/
noncomputable def zb : Fl az ℓ := red az ℓ ⟨(zK az), pInt_zK⟩

lemma Cong_zK : Cong ℓ (zK az) (zb az ℓ) := ⟨pInt_zK, rfl⟩

lemma Cong_zK_inv : Cong ℓ (zK az)⁻¹ (zb az ℓ)⁻¹ := by
  have h : zb az ℓ ≠ 0 := by
    intro h0
    have := Cong_mul (Cong_zK (ℓ := ℓ)) (Cong_red ⟨(zK az)⁻¹, pInt_zK_inv⟩)
    rw [mul_inv_cancel₀ zK_ne_zero, h0, zero_mul] at this
    exact one_ne_zero (Cong_one.unique this)
  exact Cong_inv Cong_zK h pInt_zK_inv

lemma zb_ne_zero : zb az ℓ ≠ 0 := by
  intro h0
  have := Cong_mul (Cong_zK (ℓ := ℓ)) (Cong_red ⟨(zK az)⁻¹, pInt_zK_inv⟩)
  rw [mul_inv_cancel₀ zK_ne_zero, h0, zero_mul] at this
  exact one_ne_zero (Cong_one.unique this)

lemma Cong_zK_zpow (k : ℤ) : Cong ℓ ((zK az) ^ k) (zb az ℓ ^ k) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · simpa using Cong_pow (Cong_zK (ℓ := ℓ)) n
  · rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, ← inv_pow, ← inv_pow]
    exact Cong_pow Cong_zK_inv n

/-- `1 − z̄² = az·z̄`. -/
lemma one_sub_zb_sq : 1 - zb az ℓ ^ 2 = ((az : ℕ) : Fl az ℓ) * zb az ℓ := by
  have h1 := Cong_sub (Cong_one (ℓ := ℓ)) (Cong_pow (Cong_zK (az := az) (ℓ := ℓ)) 2)
  have h2 := Cong_mul (Cong_natCast (az := az) (ℓ := ℓ) az) (Cong_zK (ℓ := ℓ))
  rw [one_sub_zK_sq] at h1
  exact h1.unique h2

lemma natCast_ne_zero_Fl {n : ℕ} (hn : ¬ ℓ ∣ n) : (n : Fl az ℓ) ≠ 0 := by
  rwa [Ne, CharP.cast_eq_zero_iff (Fl az ℓ) ℓ]

lemma two_ne_zero_Fl (hℓ2 : ℓ ≠ 2) : (2 : Fl az ℓ) ≠ 0 := by
  have := natCast_ne_zero_Fl (az := az) (ℓ := ℓ) (n := 2) (fun hd =>
    hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_two).mp hd))
  simpa using this

lemma four_ne_zero_Fl (hℓ2 : ℓ ≠ 2) : (4 : Fl az ℓ) ≠ 0 := by
  rw [show (4 : Fl az ℓ) = 2 * 2 by norm_num]; exact mul_ne_zero (two_ne_zero_Fl hℓ2) (two_ne_zero_Fl hℓ2)

/-- `az` is a unit mod `𝔩` when `ℓ ∤ 2az`. -/
lemma az_ne_zero_Fl (hℓm : ¬ ℓ ∣ 2 * az) : ((az : ℕ) : Fl az ℓ) ≠ 0 :=
  natCast_ne_zero_Fl (fun h => hℓm (Dvd.dvd.mul_left h 2))

omit [Fact (1 ≤ az)] hℓ in
lemma ne_two_of_not_dvd (hℓm : ¬ ℓ ∣ 2 * az) : ℓ ≠ 2 := by
  rintro rfl; exact hℓm (dvd_mul_right 2 az)

end LP
end Chi2U
