/-
# Dual certificates for Theorem B′, part 2: from checked data to a `DualCertU`

`CDataU` is the raw certificate: grid `1/L`, cell width `s/L`, `K` cells with heights `cs ∈ [0, 1]` (the step density
`μ`), region `[0, X]`, the log table, `λ`, the cell bounds `S_k`, a lower bound `E_lo` for `E(μ)`, rational bounds
`zlo ≤ z ≤ zhi` for `z = √5 − 2` and a dyadic enclosure `[lwlo, lwhi]` of `log z`.
`CDataU.Valid` collects the decidable checks; `toCert` builds the `DualCertU` and `Phi_le` bounds its exponent by the
rational `PhiQ = −E_lo + λ + (1/L) Σ_k (S_k − λ)₊`.

The identity `2U^μ(x) + v(x) = Σ_j D_j ψ(x − α_j/L) + x log z` (`F_eq`) is summation by parts
(`D_j = 2(c_j − c_{j−1})` at `α_j = js`, plus `−ψ(x+1)/2` and `+ψ(x−1)/2` from `v = x log z − (ψ(x+1) − ψ(x−1))/2`).
On each grid cell every term is bounded above by a linear function (chord where `D_j ψ(· − α_j/L)` is convex, tangent
where it is concave: `Core.termIV_sound`), so the sum is bounded by the larger of its two endpoint values. This keeps the
linear parts of all terms together (the cancellation in `U′`), so it is not a per-cell-maximum bound; the only loss is
the second-order chord/tangent error of each term.
Adapted from `lean_chi2/Chi2Irrational/Cert/Instance.lean` (χ₂'s `CData`).
-/
import Chi2U.Cert.Core
import Chi2U.Analytic.TheoremBU

namespace Chi2U.Cert

open Chi2U Chi2U.Interval IV Finset

/-- Raw certificate data. -/
structure CDataU where
  L : ℕ
  s : ℕ
  K : ℕ
  X : ℕ
  tab : LTree
  cs : List ℚ
  lam : ℚ
  Sks : List ℚ
  Elo : ℚ
  zlo : ℚ
  zhi : ℚ
  lwlo : ℚ
  lwhi : ℚ

lemma getD_zero_or_mem (l : List ℚ) (j : ℕ) : l.getD j 0 = 0 ∨ l.getD j 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[j]? with
  | none => left; rfl
  | some v =>
    right
    rw [List.getElem?_eq_some_iff] at h
    obtain ⟨hj, rfl⟩ := h
    exact List.getElem_mem hj

lemma sum_range_getD (l : List ℚ) (g : ℚ → ℝ) :
    ∑ j ∈ range l.length, g (l.getD j 0) = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons t ts ih =>
    rw [List.length_cons, sum_range_succ', List.map_cons, List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]; ring

lemma abel_sum (cc f : ℕ → ℝ) (K : ℕ) (hK : cc K = 0) :
    ∑ j ∈ range K, cc j * (f j - f (j + 1)) =
      ∑ j ∈ range (K + 1), (cc j - if j = 0 then 0 else cc (j - 1)) * f j := by
  have h1 : ∑ j ∈ range (K + 1), cc j * f j = ∑ j ∈ range K, cc j * f j := by
    rw [sum_range_succ, hK, zero_mul, add_zero]
  have h2 : ∑ j ∈ range (K + 1), (if j = 0 then 0 else cc (j - 1)) * f j = ∑ j ∈ range K, cc j * f (j + 1) := by
    rw [sum_range_succ']; simp
  calc ∑ j ∈ range K, cc j * (f j - f (j + 1))
      = ∑ j ∈ range K, cc j * f j - ∑ j ∈ range K, cc j * f (j + 1) := by
        rw [← sum_sub_distrib]; exact sum_congr rfl (fun j _ => by ring)
    _ = _ := by
        rw [← h1, ← h2, ← sum_sub_distrib]; exact sum_congr rfl (fun j _ => by ring)

/-! ### The enclosure of `log z` -/

/-- `[lo(log zlo), hi(log zhi)]`. -/
def lzRaw (zlo zhi : ℚ) : IV :=
  match logPt 30 zlo, logPt 30 zhi with
  | ival a _, ival _ b => ival a b
  | _, _ => top

lemma mem_lzRaw {zlo zhi : ℚ} (h0 : 0 < zlo) (hlo : (zlo : ℝ) ≤ (zU 4)) (hhi : (zU 4) ≤ zhi) :
    (lzRaw zlo zhi).mem (Real.log (zU 4)) := by
  have l1 : Real.log zlo ≤ Real.log (zU 4) := Real.log_le_log (by exact_mod_cast h0) hlo
  have l2 : Real.log (zU 4) ≤ Real.log zhi := Real.log_le_log zU_pos hhi
  have m1 := mem_logPt 30 zlo
  have m2 := mem_logPt 30 zhi
  unfold lzRaw
  revert m1 m2
  cases logPt 30 zlo <;> cases logPt 30 zhi <;> intro m1 m2
  · trivial
  · trivial
  · trivial
  · exact ⟨m1.1.trans l1, l2.trans m2.2⟩

lemma zlo_le {q : ℚ} (h2 : 0 ≤ q + 2) (h : (q + 2) ^ 2 ≤ 5) : (q : ℝ) ≤ (zU 4) := by
  have h2' : (0 : ℝ) ≤ (q : ℝ) + 2 := by exact_mod_cast h2
  have h' : ((q : ℝ) + 2) ^ 2 ≤ 5 := by exact_mod_cast h
  have : (q : ℝ) + 2 ≤ Real.sqrt 5 := by
    rw [← Real.sqrt_sq h2']; exact Real.sqrt_le_sqrt h'
  rw [zU_four]; linarith

lemma le_zhi {q : ℚ} (h2 : 0 ≤ q + 2) (h : 5 ≤ (q + 2) ^ 2) : (zU 4) ≤ (q : ℝ) := by
  have h2' : (0 : ℝ) ≤ (q : ℝ) + 2 := by exact_mod_cast h2
  have h' : (5 : ℝ) ≤ ((q : ℝ) + 2) ^ 2 := by exact_mod_cast h
  have : Real.sqrt 5 ≤ (q : ℝ) + 2 := by
    rw [← Real.sqrt_sq h2']; exact Real.sqrt_le_sqrt h'
  rw [zU_four]; linarith

namespace CDataU

variable (d : CDataU)

def c (j : ℕ) : ℚ := d.cs.getD j 0

def D (j : ℕ) : ℚ :=
  if j ≤ d.K then 2 * (d.c j - (if j = 0 then 0 else d.c (j - 1))) else if j = d.K + 1 then -1 / 2 else 1 / 2

def α (j : ℕ) : ℤ := if j ≤ d.K then ((j * d.s : ℕ) : ℤ) else if j = d.K + 1 then -(d.L : ℤ) else (d.L : ℤ)

/-- The enclosure of `log z` used in the cell checks. -/
def lw : IV := ival d.lwlo d.lwhi

def Sk (k : ℕ) : ℚ := d.Sks.getD k 0

def σQ : ℚ := (d.Sks.map (fun v => max (v - d.lam) 0)).sum

/-- The certified exponent. -/
def PhiQ : ℚ := -d.Elo + d.lam + 1 / d.L * d.σQ

/-- The cell checks on `[lo, lo + n)`. -/
def cellsOK (lo n : ℕ) : Bool :=
  (List.range' lo n).all (fun k => cellOK d.tab d.L k d.D d.α d.lw (d.K + 3) (d.Sk k))

def EOK : Bool := (EIV d.tab d.s d.L d.c d.K).loGe d.Elo

/-- `[lwlo, lwhi]` contains the series enclosure of `log z`. -/
def lwOK : Bool := (lzRaw d.zlo d.zhi).loGe d.lwlo && (lzRaw d.zlo d.zhi).hiLe d.lwhi

def tailOK : Bool :=
  (d.lw.add (ofRat (1 / (d.X : ℚ)))).hiLt 0 &&
    ((((tabIV d.tab d.X).smul 2).sub (tabIV d.tab (d.X - 1))).add (d.lw.smul (d.X : ℚ))).hiLt d.lam

lemma cells_of (lo n : ℕ) (h : d.cellsOK lo n = true) (k : ℕ) (hk1 : lo ≤ k) (hk2 : k < lo + n) :
    cellOK d.tab d.L k d.D d.α d.lw (d.K + 3) (d.Sk k) = true := by
  unfold cellsOK at h
  rw [List.all_eq_true] at h
  exact h k (List.mem_range'_1.mpr ⟨hk1, hk2⟩)

/-- All cells from chunks `[n i, n i + n)`, `i < m`. -/
lemma cells_of_chunks (n m : ℕ) (h : ∀ i < m, d.cellsOK (n * i) n = true) (hX : d.X * d.L ≤ n * m) :
    ∀ k < d.X * d.L, cellOK d.tab d.L k d.D d.α d.lw (d.K + 3) (d.Sk k) = true := by
  intro k hk
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; rw [zero_mul] at hX; omega
    · exact h0
  have e := Nat.div_add_mod k n
  have hm := Nat.mod_lt k hn
  have hq : k / n < m := (Nat.div_lt_iff_lt_mul hn).2 (by rw [mul_comm]; omega)
  exact d.cells_of (n * (k / n)) n (h _ hq) k (by omega) (by omega)

/-- The checks. -/
structure Valid : Prop where
  L1 : 1 ≤ d.L
  X4 : 4 ≤ d.X
  Ks : d.K * d.s ≤ 2 * d.L
  len : d.cs.length = d.K
  slen : d.Sks.length = d.X * d.L
  crange : ∀ v ∈ d.cs, 0 ≤ v ∧ v ≤ 1
  mass : d.cs.sum * d.s = d.L
  zlo0 : 0 < d.zlo
  zlo5 : (d.zlo + 2) ^ 2 ≤ 5
  zhi2 : 0 ≤ d.zhi + 2
  zhi5 : 5 ≤ (d.zhi + 2) ^ 2
  lw : d.lwOK = true
  tab : checkTab d.tab = true
  cells : ∀ k < d.X * d.L, cellOK d.tab d.L k d.D d.α d.lw (d.K + 3) (d.Sk k) = true
  tail : d.tailOK = true
  E : d.EOK = true

variable {d}

lemma c_nonneg (hv : d.Valid) (j : ℕ) : 0 ≤ d.c j := by
  rcases getD_zero_or_mem d.cs j with h | h
  · unfold c; rw [h]
  · exact (hv.crange _ h).1

lemma c_le_one (hv : d.Valid) (j : ℕ) : d.c j ≤ 1 := by
  rcases getD_zero_or_mem d.cs j with h | h
  · unfold c; rw [h]; norm_num
  · exact (hv.crange _ h).2

lemma c_K (hv : d.Valid) : d.c d.K = 0 := by
  unfold c; exact List.getD_eq_default _ _ (by rw [hv.len])

/-- The step density of the certificate. -/
noncomputable def μ (hv : d.Valid) : StepData where
  K := d.K
  a := fun j => ((j * d.s : ℕ) : ℝ) / d.L
  c := fun j => (d.c j : ℝ)
  a0 := by simp
  amono := fun j => div_le_div_of_nonneg_right (by exact_mod_cast Nat.mul_le_mul_right _ (Nat.le_succ j))
    (Nat.cast_nonneg _)
  c0 := fun j => by exact_mod_cast c_nonneg hv j
  c2 := fun j => by
    have : (d.c j : ℝ) ≤ 1 := by exact_mod_cast c_le_one hv j
    linarith
  mass := by
    have hL : (0 : ℝ) < d.L := by exact_mod_cast (by have := hv.L1; omega : 0 < d.L)
    have e : ∀ j ∈ range d.K, (d.c j : ℝ) * ((((j + 1) * d.s : ℕ) : ℝ) / d.L - ((j * d.s : ℕ) : ℝ) / d.L) =
        (d.s : ℝ) / d.L * (d.c j : ℝ) := fun j _ => by push_cast; ring
    rw [sum_congr rfl e, ← mul_sum]
    have hs := sum_range_getD d.cs (fun v => (v : ℝ))
    rw [hv.len] at hs
    simp only [c]
    rw [hs]
    have hm : ((d.cs.sum * d.s : ℚ) : ℝ) = (d.L : ℝ) := by exact_mod_cast hv.mass
    push_cast at hm
    rw [show (List.map (fun v : ℚ => (v : ℝ)) d.cs) = List.map Rat.cast d.cs from rfl]
    field_simp
    linarith

lemma mem_lw (hv : d.Valid) : d.lw.mem (Real.log (zU 4)) := by
  have hm := mem_lzRaw hv.zlo0 (zlo_le (by have := hv.zlo0; linarith) hv.zlo5) (le_zhi hv.zhi2 hv.zhi5)
  have h := hv.lw
  simp only [lwOK, Bool.and_eq_true] at h
  exact ⟨ge_of_loGe hm h.1, le_of_hiLe hm h.2⟩

/-- `2U + v` as a sum of `ψ`-terms. -/
lemma F_eq (hv : d.Valid) (x : ℝ) :
    2 * (μ hv).U x + vU 4 x =
      ∑ j ∈ range (d.K + 3), (d.D j : ℝ) * psiF (x - (d.α j : ℝ) / d.L) + x * Real.log (zU 4) := by
  have hL : (d.L : ℝ) ≠ 0 := by exact_mod_cast (by have := hv.L1; omega : d.L ≠ 0)
  have hU : 2 * (μ hv).U x = ∑ j ∈ range (d.K + 1), (d.D j : ℝ) * psiF (x - (d.α j : ℝ) / d.L) := by
    unfold StepData.U Uint
    simp only [μ]
    rw [mul_sum]
    have := abel_sum (fun j => 2 * (d.c j : ℝ)) (fun j => psiF (x - ((j * d.s : ℕ) : ℝ) / d.L)) d.K
      (by simp [c_K hv])
    rw [show ∑ j ∈ range d.K, 2 * ((d.c j : ℝ) * (psiF (x - ((j * d.s : ℕ) : ℝ) / d.L) -
        psiF (x - (((j + 1) * d.s : ℕ) : ℝ) / d.L))) = ∑ j ∈ range d.K, 2 * (d.c j : ℝ) *
        (psiF (x - ((j * d.s : ℕ) : ℝ) / d.L) - psiF (x - (((j + 1) * d.s : ℕ) : ℝ) / d.L)) from
      sum_congr rfl (fun j _ => by ring), this]
    refine sum_congr rfl (fun j hj => ?_)
    have hjK : j ≤ d.K := by have := mem_range.mp hj; omega
    simp only [D, α, ite_eq_left hjK]
    push_cast
    split_ifs <;> push_cast <;> ring
  rw [show d.K + 3 = d.K + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ← hU]
  have h1 : d.D (d.K + 1) = -1 / 2 := by simp [D]
  have h2 : d.α (d.K + 1) = -(d.L : ℤ) := by simp [α]
  have h3 : d.D (d.K + 1 + 1) = 1 / 2 := by simp [D]
  have h4 : d.α (d.K + 1 + 1) = (d.L : ℤ) := by simp [α]
  rw [h1, h2, h3, h4]
  unfold vU PsiU
  push_cast
  rw [show x - -(d.L : ℝ) / d.L = x + 1 by rw [neg_div, div_self hL]; ring,
    show x - (d.L : ℝ) / d.L = x - 1 by rw [div_self hL]]
  ring

/-- **The `DualCertU` of checked data.** -/
noncomputable def toCert (hv : d.Valid) : DualCertU 4 where
  μ := μ hv
  hc1 := fun j => by
    change (d.c j : ℝ) ≤ 1
    exact_mod_cast c_le_one hv j
  hsupp := by
    change ((d.K * d.s : ℕ) : ℝ) / d.L ≤ 2
    have hL : (0 : ℝ) < d.L := by exact_mod_cast (by have := hv.L1; omega : 0 < d.L)
    rw [div_le_iff₀ hL]
    exact_mod_cast hv.Ks
  lam := d.lam
  L := d.L
  X := d.X
  Sk := fun k => (d.Sk k : ℝ)
  hL := hv.L1
  hX := hv.X4
  hF := by
    intro k hk x hx0 hx1
    have hL : 0 < d.L := by have := hv.L1; omega
    have := cellOK_sound hv.tab hL d.D d.α (mem_lw hv) (d.K + 3) (hv.cells k hk) hx0 hx1
    rw [F_eq hv]
    exact this
  htail1 := by
    have h := hv.tail
    simp only [tailOK, Bool.and_eq_true] at h
    have := lt_of_hiLt (IV.mem_add (mem_lw hv) (mem_ofRat (1 / (d.X : ℚ)))) h.1
    push_cast at this
    linarith
  htail2 := by
    have h := hv.tail
    simp only [tailOK, Bool.and_eq_true] at h
    have := lt_of_hiLt (IV.mem_add (mem_sub (mem_smul 2 (mem_tabIV hv.tab d.X)) (mem_tabIV hv.tab (d.X - 1)))
      (mem_smul (d.X : ℚ) (mem_lw hv))) h.2
    have hX1 : 1 ≤ d.X := by have := hv.X4; omega
    rw [Nat.cast_sub hX1, Nat.cast_one] at this
    push_cast at this
    linarith

/-- **The certified exponent.** -/
theorem Phi_le (hv : d.Valid) : (toCert hv).Phi ≤ (d.PhiQ : ℝ) := by
  -- `E(μ) ≥ E_lo`
  have hE : (d.Elo : ℝ) ≤ (μ hv).E := by
    have hm := mem_EIV hv.tab d.s (by have := hv.L1; omega : 0 < d.L) d.c d.K
    have := ge_of_loGe hm hv.E
    exact this
  -- `σ = σQ`
  have hσ : (toCert hv).σ = (d.σQ : ℝ) := by
    change ∑ k ∈ range (d.X * d.L), max ((d.Sk k : ℝ) - d.lam) 0 = _
    rw [← hv.slen]
    have := sum_range_getD d.Sks (fun v => max ((v : ℝ) - d.lam) 0)
    simp only [Sk]
    rw [this]
    unfold σQ
    push_cast
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left (fun v _ => ?_))
    simp
  unfold DualCertU.Phi PhiQ
  rw [hσ]
  change -(μ hv).E + (d.lam : ℝ) + 1 / (d.L : ℝ) * (d.σQ : ℝ) ≤ _
  push_cast
  linarith

end CDataU

end Chi2U.Cert
