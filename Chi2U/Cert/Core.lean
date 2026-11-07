/-
# Dual certificates, part 1: kernel-checked enclosures

* `checkTab`, `tabIV`: a table of `log n` (`n = 1, 2, …`, stored as a Braun tree `LTree`) as dyadic intervals of width `2·2^{-40}`, each entry checked
  against the series enclosure `logPt` (`mem_tabIV`);
* `logQ`, `psiQ`, `PsiQ`: enclosures of `log|u|`, `ψ(u)`, `Ψ(u)` at `u = num/den`;
* `termIV`: for `x ∈ [k/L, (k+1)/L]`, a linear upper bound of `D ψ(x − α/L)` (`α ∈ ℤ`), given by enclosures of its values
  at the two endpoints: the chord where `D ψ(· − α/L)` is convex, the tangent (at the midpoint, or at the endpoint away
  from `α/L`) where it is concave (`termIV_sound`);
* `sum0`, `sum1`, `sum_sound`: the sum over terms plus the linear term `x log W`;
* `GQ`, `EIV`: enclosures of the cell–cell energies `∫∫ log|x − y|` and of `E(μ)` for a step density on the grid `s/L`.
Copied from `lean_chi2/Chi2Irrational/Cert/Core.lean` (namespace `Chi2Irr` → `Chi2U`); changes: the import
(`StepMu` instead of `TheoremB`), a local copy `psiF_neg_cert` of lean_chi2's `psiF_neg`, the log table stored as a
Braun tree (`LTree`, logarithmic lookup; the 2000-entry list made the kernel checks slow), and `termZ`, which skips
terms with `D = 0`.
-/
import Chi2U.Interval.Log
import Chi2U.Analytic.StepMu

namespace Chi2U.Cert

open Chi2U Chi2U.Interval IV Finset

/-! ### The log table -/

/-- Table precision: entries are multiples of `2^{-40}`. -/
def PB : ℕ := 40

/-- `log n ∈ [t, t + 2] · 2^{-40}`, checked against the series. -/
def entryOK (n : ℕ) (t : ℤ) : Bool :=
  (logPt 30 (n : ℚ)).loGe ((t : ℚ) / 2 ^ PB) && (logPt 30 (n : ℚ)).hiLe (((t : ℚ) + 2) / 2 ^ PB)

/-- The log table as a Braun tree (lookup in `O(log n)` kernel steps instead of `O(n)` for a list): index `0` at the
root, index `2i + 1` at index `i` of the left subtree, `2i + 2` at index `i` of the right subtree. -/
inductive LTree where
  | leaf : LTree
  | node (l : LTree) (v : ℤ) (r : LTree) : LTree

/-- Lookup in a Braun tree. -/
def LTree.get : LTree → ℕ → Option ℤ
  | leaf, _ => none
  | node l v r, n => if n = 0 then some v else if n % 2 = 1 then l.get (n / 2) else r.get (n / 2 - 1)

/-- Check every entry: the subtree at `(m, o)` holds the table index `m i + o` at its index `i`, which must enclose
`log (m i + o + 1)`. -/
def checkT : LTree → ℕ → ℕ → Bool
  | .leaf, _, _ => true
  | .node l v r, m, o => entryOK (o + 1) v && checkT l (2 * m) (o + m) && checkT r (2 * m) (o + 2 * m)

lemma checkT_get : ∀ (t : LTree) (m o n : ℕ) (v : ℤ), checkT t m o = true → t.get n = some v →
    entryOK (m * n + o + 1) v = true
  | .leaf, _, _, _, _, _, h => by simp [LTree.get] at h
  | .node l w r, m, o, n, v, hc, hg => by
    simp only [checkT, Bool.and_eq_true] at hc
    obtain ⟨⟨h0, hl⟩, hr⟩ := hc
    simp only [LTree.get] at hg
    split_ifs at hg with hn hodd
    · subst hn; cases hg; simpa using h0
    · have := checkT_get l (2 * m) (o + m) (n / 2) v hl hg
      have e : n = 2 * (n / 2) + 1 := by omega
      rw [e]; convert this using 2; ring
    · have := checkT_get r (2 * m) (o + 2 * m) (n / 2 - 1) v hr hg
      obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 2 := ⟨n / 2 - 1, by omega⟩
      have e : n / 2 - 1 = k := by omega
      rw [e] at this; rw [hk]; convert this using 2; ring

/-- The table check: entry `i` of the table encloses `log (i + 1)`. -/
def checkTab (t : LTree) : Bool := checkT t 1 0

/-- The table lookup (`top` outside the table). -/
def tabIV (tab : LTree) (n : ℕ) : IV :=
  if n = 0 then top else
    match tab.get (n - 1) with
    | some t => ival ((t : ℚ) / 2 ^ PB) (((t : ℚ) + 2) / 2 ^ PB)
    | none => top

lemma mem_tabIV {tab : LTree} (hok : checkTab tab = true) (n : ℕ) :
    (tabIV tab n).mem (Real.log n) := by
  unfold tabIV
  split_ifs with hn
  · trivial
  · cases h : tab.get (n - 1) with
    | none => trivial
    | some t =>
      have := checkT_get tab 1 0 (n - 1) t hok h
      rw [show 1 * (n - 1) + 0 + 1 = n by omega] at this
      simp only [entryOK, Bool.and_eq_true] at this
      have hm := mem_logPt 30 (n : ℚ)
      push_cast at hm
      exact ⟨ge_of_loGe hm this.1, le_of_hiLe hm this.2⟩

/-! ### `log|u|`, `ψ(u)`, `Ψ(u)` at `u = num/den` -/

def logQ (tab : LTree) (num : ℤ) (den : ℕ) : IV := (tabIV tab num.natAbs).sub (tabIV tab den)

lemma mem_logQ {tab : LTree} (hok : checkTab tab = true) (num : ℤ) {den : ℕ} (hnum : num ≠ 0)
    (hden : 0 < den) : (logQ tab num den).mem (Real.log ((num : ℝ) / den)) := by
  have h1 := mem_tabIV hok num.natAbs
  have h2 := mem_tabIV hok den
  have e : Real.log ((num : ℝ) / den) = Real.log (num.natAbs : ℝ) - Real.log den := by
    rw [Real.log_div (by exact_mod_cast hnum) (by positivity), Nat.cast_natAbs, Int.cast_abs,
      Real.log_abs]
  rw [e]; exact mem_sub h1 h2

def psiQ (tab : LTree) (num : ℤ) (den : ℕ) : IV :=
  if num = 0 then ofRat 0 else ((logQ tab num den).smul ((num : ℚ) / den)).sub (ofRat ((num : ℚ) / den))

lemma mem_psiQ {tab : LTree} (hok : checkTab tab = true) (num : ℤ) {den : ℕ} (hden : 0 < den) :
    (psiQ tab num den).mem (psiF ((num : ℝ) / den)) := by
  unfold psiQ
  split_ifs with h
  · subst h
    have := mem_ofRat 0
    simpa [psiF] using this
  · have := mem_sub (mem_smul ((num : ℚ) / den) (mem_logQ hok num h hden)) (mem_ofRat ((num : ℚ) / den))
    unfold psiF
    push_cast at this ⊢
    exact this

def PsiQ (tab : LTree) (num : ℤ) (den : ℕ) : IV :=
  if num = 0 then ofRat 0 else
    ((logQ tab num den).smul (((num : ℚ) / den) ^ 2 / 2)).sub (ofRat (3 * ((num : ℚ) / den) ^ 2 / 4))

lemma mem_PsiQ {tab : LTree} (hok : checkTab tab = true) (num : ℤ) {den : ℕ} (hden : 0 < den) :
    (PsiQ tab num den).mem (PsiF ((num : ℝ) / den)) := by
  unfold PsiQ
  split_ifs with h
  · subst h
    have := mem_ofRat 0
    simpa [PsiF] using this
  · have := mem_sub (mem_smul (((num : ℚ) / den) ^ 2 / 2) (mem_logQ hok num h hden))
      (mem_ofRat (3 * ((num : ℚ) / den) ^ 2 / 4))
    unfold PsiF
    push_cast at this ⊢
    convert this using 2; ring

/-! ### Chords and tangents of `ψ` -/

lemma psiF_neg_cert (u : ℝ) : psiF (-u) = -psiF u := by
  unfold psiF; rw [Real.log_neg_eq_log]; ring

lemma psiF_tangent_pos {p u : ℝ} (hp : 0 < p) (hu : 0 ≤ u) : psiF p + Real.log p * (u - p) ≤ psiF u := by
  rcases le_total p u with h | h
  · have := psiF_diff_ge_pos hp le_rfl h; linarith
  · have := psiF_diff_le hp h (by linarith) le_rfl (Or.inl hu); linarith

lemma psiF_tangent_neg {p u : ℝ} (hp : p < 0) (hu : u ≤ 0) : psiF u ≤ psiF p + Real.log p * (u - p) := by
  have := psiF_tangent_pos (p := -p) (u := -u) (by linarith) (by linarith)
  rw [psiF_neg_cert, psiF_neg_cert, Real.log_neg_eq_log] at this
  linarith

lemma psiF_chord_pos {a b θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    psiF ((1 - θ) * a + θ * b) ≤ (1 - θ) * psiF a + θ * psiF b := by
  have := Real.convexOn_mul_log.2 (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr hb) (by linarith : 0 ≤ 1 - θ) hθ0
    (by ring)
  simp only [smul_eq_mul] at this
  unfold psiF
  linarith

lemma psiF_chord_neg {a b θ : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) * psiF a + θ * psiF b ≤ psiF ((1 - θ) * a + θ * b) := by
  have := psiF_chord_pos (a := -a) (b := -b) (by linarith) (by linarith) hθ0 hθ1
  rw [show (1 - θ) * -a + θ * -b = -((1 - θ) * a + θ * b) by ring, psiF_neg_cert, psiF_neg_cert, psiF_neg_cert] at this
  linarith

/-! ### One term -/

/-- The tangent point (numerator over `2L`): the endpoint away from the kink, or the midpoint. -/
def tanPt (u0 : ℤ) : ℤ := if u0 = 0 then 2 else if u0 + 1 = 0 then -2 else 2 * u0 + 1

lemma tanPt_pos {u0 : ℤ} (h : 0 ≤ u0) : 0 < tanPt u0 := by
  unfold tanPt; split_ifs <;> omega

lemma tanPt_neg {u0 : ℤ} (h : u0 + 1 ≤ 0) : tanPt u0 < 0 := by
  unfold tanPt; split_ifs <;> omega

/-- Endpoint values of a linear upper bound of `D ψ(x − α/L)` on `[k/L, (k+1)/L]`. -/
def termIV (tab : LTree) (L k : ℕ) (D : ℚ) (α : ℤ) : IV × IV :=
  if (0 ≤ D ∧ 0 ≤ (k : ℤ) - α) ∨ (D ≤ 0 ∧ (k : ℤ) - α + 1 ≤ 0) then
    ((psiQ tab ((k : ℤ) - α) L).smul D, (psiQ tab ((k : ℤ) - α + 1) L).smul D)
  else
    (((psiQ tab (tanPt ((k : ℤ) - α)) (2 * L)).add ((logQ tab (tanPt ((k : ℤ) - α)) (2 * L)).smul
        (((2 * ((k : ℤ) - α) - tanPt ((k : ℤ) - α) : ℤ) : ℚ) / (2 * L)))).smul D,
     ((psiQ tab (tanPt ((k : ℤ) - α)) (2 * L)).add ((logQ tab (tanPt ((k : ℤ) - α)) (2 * L)).smul
        (((2 * ((k : ℤ) - α + 1) - tanPt ((k : ℤ) - α) : ℤ) : ℚ) / (2 * L)))).smul D)

lemma termIV_sound {tab : LTree} (hok : checkTab tab = true) {L k : ℕ} (hL : 0 < L) (D : ℚ) (α : ℤ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ y0 y1 : ℝ, (termIV tab L k D α).1.mem y0 ∧ (termIV tab L k D α).2.mem y1 ∧
      (D : ℝ) * psiF (((k : ℝ) + θ) / L - (α : ℝ) / L) ≤ (1 - θ) * y0 + θ * y1 := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  set u0 : ℤ := (k : ℤ) - α with hu0
  have hx : ((k : ℝ) + θ) / L - (α : ℝ) / L = (1 - θ) * ((u0 : ℝ) / L) + θ * (((u0 + 1 : ℤ) : ℝ) / L) := by
    rw [hu0]; push_cast; field_simp; ring
  unfold termIV
  split_ifs with hconv
  · refine ⟨(D : ℝ) * psiF ((u0 : ℝ) / L), (D : ℝ) * psiF (((u0 + 1 : ℤ) : ℝ) / L),
      mem_smul _ (mem_psiQ hok _ hL), mem_smul _ (mem_psiQ hok _ hL), ?_⟩
    rw [hx]
    rcases hconv with ⟨hD, hu⟩ | ⟨hD, hu⟩
    · have hD' : (0 : ℝ) ≤ D := by exact_mod_cast hD
      have hu' : (0 : ℝ) ≤ u0 := by exact_mod_cast hu
      have hb' : (0 : ℝ) ≤ ((u0 + 1 : ℤ) : ℝ) / L := div_nonneg (by push_cast; linarith) hL'.le
      have := psiF_chord_pos (a := (u0 : ℝ) / L) (b := ((u0 + 1 : ℤ) : ℝ) / L) (div_nonneg hu' hL'.le) hb' hθ0 hθ1
      have := mul_le_mul_of_nonneg_left this hD'
      linarith
    · have hD' : (D : ℝ) ≤ 0 := by exact_mod_cast hD
      have hu' : ((u0 + 1 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hu
      have hu'' : (u0 : ℝ) ≤ 0 := by push_cast at hu'; linarith
      have := psiF_chord_neg (a := (u0 : ℝ) / L) (b := ((u0 + 1 : ℤ) : ℝ) / L)
        (div_nonpos_of_nonpos_of_nonneg hu'' hL'.le) (div_nonpos_of_nonpos_of_nonneg hu' hL'.le) hθ0 hθ1
      have := mul_le_mul_of_nonpos_left this hD'
      linarith
  · set pn := tanPt u0 with hpn
    set p : ℝ := (pn : ℝ) / ((2 * L : ℕ) : ℝ) with hp
    have hpn0 : pn ≠ 0 := by
      rcases le_or_gt 0 u0 with h | h
      · exact (tanPt_pos h).ne'
      · exact (tanPt_neg (by omega)).ne
    have h2L : 0 < 2 * L := by omega
    set r0 : ℚ := ((2 * u0 - pn : ℤ) : ℚ) / (2 * L)
    set r1 : ℚ := ((2 * (u0 + 1) - pn : ℤ) : ℚ) / (2 * L)
    refine ⟨(D : ℝ) * (psiF p + (r0 : ℝ) * Real.log p), (D : ℝ) * (psiF p + (r1 : ℝ) * Real.log p),
      mem_smul _ (mem_add (mem_psiQ hok _ h2L) (mem_smul _ (mem_logQ hok _ hpn0 h2L))),
      mem_smul _ (mem_add (mem_psiQ hok _ h2L) (mem_smul _ (mem_logQ hok _ hpn0 h2L))), ?_⟩
    have hr : (1 - θ) * (r0 : ℝ) + θ * (r1 : ℝ) = (1 - θ) * ((u0 : ℝ) / L) + θ * (((u0 + 1 : ℤ) : ℝ) / L) - p := by
      simp only [r0, r1, hp]; push_cast; field_simp; ring
    rw [hx]
    set u := (1 - θ) * ((u0 : ℝ) / L) + θ * (((u0 + 1 : ℤ) : ℝ) / L) with hu
    have key : (1 - θ) * ((D : ℝ) * (psiF p + (r0 : ℝ) * Real.log p)) + θ * ((D : ℝ) * (psiF p + (r1 : ℝ) *
        Real.log p)) = (D : ℝ) * (psiF p + Real.log p * (u - p)) := by
      rw [← hr]; ring
    rw [key]
    rcases le_or_gt 0 u0 with h | h
    · -- `u ≥ 0`, so `D < 0`
      have hD : (D : ℝ) < 0 := by
        have : ¬ (0 ≤ D) := fun hD => hconv (Or.inl ⟨hD, h⟩)
        exact_mod_cast (not_le.mp this)
      have hp0 : 0 < p := div_pos (by exact_mod_cast tanPt_pos h) (by positivity)
      have hu0' : (0 : ℝ) ≤ u := by
        have : (0 : ℝ) ≤ u0 := by exact_mod_cast h
        rw [hu]; push_cast
        have := div_nonneg this hL'.le
        have : (0 : ℝ) ≤ ((u0 : ℝ) + 1) / L := div_nonneg (by linarith) hL'.le
        nlinarith
      have := psiF_tangent_pos hp0 hu0'
      nlinarith
    · -- `u ≤ 0`, so `D > 0`
      have h' : u0 + 1 ≤ 0 := by omega
      have hD : 0 < (D : ℝ) := by
        have : ¬ (D ≤ 0) := fun hD => hconv (Or.inr ⟨hD, h'⟩)
        exact_mod_cast (not_le.mp this)
      have hp0 : p < 0 := div_neg_of_neg_of_pos (by exact_mod_cast tanPt_neg h') (by positivity)
      have hu0' : u ≤ 0 := by
        have : ((u0 : ℝ) + 1) ≤ 0 := by exact_mod_cast h'
        rw [hu]; push_cast
        have : ((u0 : ℝ) + 1) / L ≤ 0 := div_nonpos_of_nonpos_of_nonneg this hL'.le
        have : (u0 : ℝ) / L ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hL'.le
        nlinarith
      have := psiF_tangent_neg hp0 hu0'
      nlinarith

/-- `termIV`, skipping terms with `D = 0`. -/
def termZ (tab : LTree) (L k : ℕ) (D : ℚ) (α : ℤ) : IV × IV :=
  if D = 0 then (ofRat 0, ofRat 0) else termIV tab L k D α

lemma termZ_sound {tab : LTree} (hok : checkTab tab = true) {L k : ℕ} (hL : 0 < L) (D : ℚ) (α : ℤ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ y0 y1 : ℝ, (termZ tab L k D α).1.mem y0 ∧ (termZ tab L k D α).2.mem y1 ∧
      (D : ℝ) * psiF (((k : ℝ) + θ) / L - (α : ℝ) / L) ≤ (1 - θ) * y0 + θ * y1 := by
  unfold termZ
  split_ifs with hD
  · refine ⟨0, 0, ?_, ?_, ?_⟩
    · have := mem_ofRat 0; simpa using this
    · have := mem_ofRat 0; simpa using this
    · subst hD; simp
  · exact termIV_sound hok hL D α hθ0 hθ1

/-! ### The sum over terms -/

/-- Enclosure at the left endpoint of `Σ_{j<n} (linear bound of D_j ψ(x − α_j/L)) + x log W`. -/
def sum0 (tab : LTree) (L k : ℕ) (D : ℕ → ℚ) (α : ℕ → ℤ) (lw : IV) : ℕ → IV
  | 0 => lw.smul ((k : ℚ) / L)
  | n + 1 => (termZ tab L k (D n) (α n)).1.add (sum0 tab L k D α lw n)

/-- The same at the right endpoint. -/
def sum1 (tab : LTree) (L k : ℕ) (D : ℕ → ℚ) (α : ℕ → ℤ) (lw : IV) : ℕ → IV
  | 0 => lw.smul (((k : ℚ) + 1) / L)
  | n + 1 => (termZ tab L k (D n) (α n)).2.add (sum1 tab L k D α lw n)

lemma sum_sound {tab : LTree} (hok : checkTab tab = true) {L k : ℕ} (hL : 0 < L) (D : ℕ → ℚ) (α : ℕ → ℤ)
    {lw : IV} {w : ℝ} (hw : lw.mem w) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (n : ℕ) :
    ∃ Y0 Y1 : ℝ, (sum0 tab L k D α lw n).mem Y0 ∧ (sum1 tab L k D α lw n).mem Y1 ∧
      ∑ j ∈ range n, (D j : ℝ) * psiF (((k : ℝ) + θ) / L - (α j : ℝ) / L) + ((k : ℝ) + θ) / L * w ≤
        (1 - θ) * Y0 + θ * Y1 := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  induction n with
  | zero =>
    refine ⟨(((k : ℚ) / L : ℚ) : ℝ) * w, ((((k : ℚ) + 1) / L : ℚ) : ℝ) * w, mem_smul _ hw, mem_smul _ hw, ?_⟩
    simp only [range_zero, sum_empty, zero_add]
    push_cast
    apply le_of_eq
    field_simp; ring
  | succ n ih =>
    obtain ⟨Y0, Y1, h0, h1, hle⟩ := ih
    obtain ⟨y0, y1, g0, g1, gle⟩ := termZ_sound hok (k := k) hL (D n) (α n) hθ0 hθ1
    refine ⟨y0 + Y0, y1 + Y1, mem_add g0 h0, mem_add g1 h1, ?_⟩
    rw [sum_range_succ]
    linarith

/-- The check on one grid cell. -/
def cellOK (tab : LTree) (L k : ℕ) (D : ℕ → ℚ) (α : ℕ → ℤ) (lw : IV) (n : ℕ) (S : ℚ) : Bool :=
  (sum0 tab L k D α lw n).hiLe S && (sum1 tab L k D α lw n).hiLe S

lemma cellOK_sound {tab : LTree} (hok : checkTab tab = true) {L k : ℕ} (hL : 0 < L) (D : ℕ → ℚ)
    (α : ℕ → ℤ) {lw : IV} {w : ℝ} (hw : lw.mem w) (n : ℕ) {S : ℚ} (hc : cellOK tab L k D α lw n S = true)
    {x : ℝ} (hx0 : (k : ℝ) / L ≤ x) (hx1 : x ≤ ((k : ℝ) + 1) / L) :
    ∑ j ∈ range n, (D j : ℝ) * psiF (x - (α j : ℝ) / L) + x * w ≤ S := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  set θ := x * L - k with hθ
  have hθ0 : 0 ≤ θ := by rw [div_le_iff₀ hL'] at hx0; linarith
  have hθ1 : θ ≤ 1 := by rw [le_div_iff₀ hL'] at hx1; linarith
  have hxθ : x = ((k : ℝ) + θ) / L := by rw [hθ]; field_simp; ring
  simp only [cellOK, Bool.and_eq_true] at hc
  obtain ⟨Y0, Y1, h0, h1, hle⟩ := sum_sound hok hL D α hw hθ0 hθ1 n
  have a0 := le_of_hiLe h0 hc.1
  have a1 := le_of_hiLe h1 hc.2
  rw [hxθ]
  nlinarith

/-! ### The energy -/

/-- `Σ_{i<n} I_i`. -/
def ivSum (I : ℕ → IV) : ℕ → IV
  | 0 => ofRat 0
  | n + 1 => (I n).add (ivSum I n)

lemma mem_ivSum (I : ℕ → IV) (x : ℕ → ℝ) (h : ∀ i, (I i).mem (x i)) (n : ℕ) :
    (ivSum I n).mem (∑ i ∈ range n, x i) := by
  induction n with
  | zero =>
    have := mem_ofRat 0
    rw [Rat.cast_zero] at this
    simpa [ivSum] using this
  | succ n ih => rw [sum_range_succ, add_comm (∑ i ∈ range n, x i)]; exact IV.mem_add (h n) ih

/-- `∫_{cell j} ∫_{cell j'} log|x − y|` for cells of width `s/L` at distance `d = j − j'`. -/
def GQ (tab : LTree) (s L : ℕ) (d : ℤ) : IV :=
  ((PsiQ tab ((d + 1) * s) L).add (PsiQ tab ((d - 1) * s) L)).sub ((PsiQ tab (d * s) L).smul 2)

lemma mem_GQ {tab : LTree} (hok : checkTab tab = true) (s : ℕ) {L : ℕ} (hL : 0 < L) (j j' : ℕ) :
    (GQ tab s L ((j : ℤ) - j')).mem (Gint ((j * s : ℕ) / (L : ℝ)) (((j + 1) * s : ℕ) / (L : ℝ))
      ((j' * s : ℕ) / (L : ℝ)) (((j' + 1) * s : ℕ) / (L : ℝ))) := by
  have h1 := mem_PsiQ hok ((((j : ℤ) - j') + 1) * s) hL
  have h2 := mem_PsiQ hok ((((j : ℤ) - j') - 1) * s) hL
  have h3 := mem_smul 2 (mem_PsiQ hok (((j : ℤ) - j') * s) hL)
  have := mem_sub (mem_add h1 h2) h3
  unfold GQ Gint
  convert this using 1
  push_cast
  have e1 : ((j : ℝ) + 1) * s / L - (j' : ℝ) * s / L = (((j : ℝ) - j') + 1) * s / L := by ring
  have e2 : (j : ℝ) * s / L - ((j' : ℝ) + 1) * s / L = (((j : ℝ) - j') - 1) * s / L := by ring
  have e3 : ((j : ℝ) + 1) * s / L - ((j' : ℝ) + 1) * s / L = ((j : ℝ) - j') * s / L := by ring
  have e4 : (j : ℝ) * s / L - (j' : ℝ) * s / L = ((j : ℝ) - j') * s / L := by ring
  rw [e1, e2, e3, e4]; ring

/-- The enclosure of `E(μ) = Σ_{j,j'} c_j c_{j'} G(j − j')`. -/
def EIV (tab : LTree) (s L : ℕ) (c : ℕ → ℚ) (K : ℕ) : IV :=
  ivSum (fun j => ivSum (fun j' => (GQ tab s L ((j : ℤ) - j')).smul (c j * c j')) K) K

lemma mem_EIV {tab : LTree} (hok : checkTab tab = true) (s : ℕ) {L : ℕ} (hL : 0 < L) (c : ℕ → ℚ) (K : ℕ) :
    (EIV tab s L c K).mem (∑ j ∈ range K, ∑ j' ∈ range K, (c j : ℝ) * (c j' : ℝ) *
      Gint ((j * s : ℕ) / (L : ℝ)) (((j + 1) * s : ℕ) / (L : ℝ)) ((j' * s : ℕ) / (L : ℝ))
        (((j' + 1) * s : ℕ) / (L : ℝ))) := by
  refine mem_ivSum _ _ (fun j => mem_ivSum _ _ (fun j' => ?_) K) K
  have := mem_smul (c j * c j') (mem_GQ hok s hL j j')
  push_cast at this ⊢
  exact this

end Chi2U.Cert
