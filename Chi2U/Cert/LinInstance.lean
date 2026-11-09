/-
# Linear-majorant certificates at any trace: from checked data to a `DualCertU az`

`CDataLin` is the raw certificate at the trace `az` (`z = zU az = (√(az² + 4) − az)/2`): grid `1/L`, cell width `s/L`,
`K` cells with heights `cs ∈ [0, 1]` (the step density `μ`), region `[0, X]`, the log table, `λ`, the endpoint values
`e0 k`, `e1 k` of the linear cell majorants, a lower bound `E_lo` for `E(μ)`, rational bounds `zlo ≤ z ≤ zhi` (checked by
`(2 zlo + az)² ≤ az² + 4 ≤ (2 zhi + az)²`) and a dyadic enclosure `[lwlo, lwhi]` of `log z`.

`CDataLin.Valid` collects the decidable checks; `toLin` builds the `LinCertU` (`Cert/Lin.lean`) and `PhiLin_le` bounds
its exponent by the rational `PhiQ = −E_lo + λ + (1/L) Σ_k ((e0 k − λ)₊ + (e1 k − λ)₊)/2`; `exists_dual_le` then gives a
`DualCertU az` with `Φ ≤ t` for every rational `t > PhiQ` (`LinCertU.exists_dual`).

The cell check `cellLinOK` is `Core.cellOK` with the two endpoint bounds kept apart: the chord/tangent linear bounds of
all terms (`Core.sum_sound`) sum to a linear bound of `2U^μ + v` on the cell, whose endpoint values are `≤ e0 k`, `≤ e1 k`.
The rest is `Cert/Instance.lean` (Theorem U's `CDataU`) with `4` replaced by `az`.
-/
import Chi2U.Cert.Instance
import Chi2U.Cert.Lin

namespace Chi2U.Cert

open Chi2U Chi2U.Interval IV Finset

/-! ### The enclosure of `z` and `log z` at a general trace -/

lemma zlo_le_az {az : ℕ} [Fact (1 ≤ az)] {q : ℚ} (h2 : 0 ≤ 2 * q + az) (h : (2 * q + az) ^ 2 ≤ (az : ℚ) ^ 2 + 4) :
    (q : ℝ) ≤ zU az := by
  have h2' : (0 : ℝ) ≤ (2 * q + az : ℚ) := by exact_mod_cast h2
  have h' : (((2 * q + az : ℚ) : ℝ) / 2) ^ 2 ≤ ((az : ℝ) / 2) ^ 2 + 1 := by
    have : (((2 * q + az : ℚ)) : ℝ) ^ 2 ≤ (az : ℝ) ^ 2 + 4 := by exact_mod_cast h
    nlinarith
  have : ((2 * q + az : ℚ) : ℝ) / 2 ≤ Real.sqrt (((az : ℝ) / 2) ^ 2 + 1) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ ((2 * q + az : ℚ) : ℝ) / 2)]
    exact Real.sqrt_le_sqrt h'
  unfold zU
  push_cast at this
  linarith

lemma le_zhi_az {az : ℕ} [Fact (1 ≤ az)] {q : ℚ} (h2 : 0 ≤ 2 * q + az) (h : (az : ℚ) ^ 2 + 4 ≤ (2 * q + az) ^ 2) :
    zU az ≤ (q : ℝ) := by
  have h2' : (0 : ℝ) ≤ (2 * q + az : ℚ) := by exact_mod_cast h2
  have h' : ((az : ℝ) / 2) ^ 2 + 1 ≤ (((2 * q + az : ℚ) : ℝ) / 2) ^ 2 := by
    have : (az : ℝ) ^ 2 + 4 ≤ (((2 * q + az : ℚ)) : ℝ) ^ 2 := by exact_mod_cast h
    nlinarith
  have : Real.sqrt (((az : ℝ) / 2) ^ 2 + 1) ≤ ((2 * q + az : ℚ) : ℝ) / 2 := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ ((2 * q + az : ℚ) : ℝ) / 2)]
    exact Real.sqrt_le_sqrt h'
  unfold zU
  push_cast at this
  linarith

lemma mem_lzRaw_az {az : ℕ} [Fact (1 ≤ az)] {zlo zhi : ℚ} (h0 : 0 < zlo) (hlo : (zlo : ℝ) ≤ zU az)
    (hhi : zU az ≤ zhi) : (lzRaw zlo zhi).mem (Real.log (zU az)) := by
  have l1 : Real.log zlo ≤ Real.log (zU az) := Real.log_le_log (by exact_mod_cast h0) hlo
  have l2 : Real.log (zU az) ≤ Real.log zhi := Real.log_le_log zU_pos hhi
  have m1 := mem_logPt 30 zlo
  have m2 := mem_logPt 30 zhi
  unfold lzRaw
  revert m1 m2
  cases logPt 30 zlo <;> cases logPt 30 zhi <;> intro m1 m2
  · trivial
  · trivial
  · trivial
  · exact ⟨m1.1.trans l1, l2.trans m2.2⟩

/-! ### The linear cell check -/

/-- The linear cell check: the endpoint values of the summed linear bound are `≤ e0`, `≤ e1`. -/
def cellLinOK (tab : LTree) (L k : ℕ) (D : ℕ → ℚ) (α : ℕ → ℤ) (lw : IV) (n : ℕ) (e0 e1 : ℚ) : Bool :=
  (sum0 tab L k D α lw n).hiLe e0 && (sum1 tab L k D α lw n).hiLe e1

lemma cellLinOK_sound {tab : LTree} (hok : checkTab tab = true) {L k : ℕ} (hL : 0 < L) (D : ℕ → ℚ)
    (α : ℕ → ℤ) {lw : IV} {w : ℝ} (hw : lw.mem w) (n : ℕ) {e0 e1 : ℚ}
    (hc : cellLinOK tab L k D α lw n e0 e1 = true)
    {x : ℝ} (hx0 : (k : ℝ) / L ≤ x) (hx1 : x ≤ ((k : ℝ) + 1) / L) :
    ∑ j ∈ range n, (D j : ℝ) * psiF (x - (α j : ℝ) / L) + x * w ≤
      (e0 : ℝ) + (x * L - k) * ((e1 : ℝ) - e0) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  set θ := x * L - k with hθ
  have hθ0 : 0 ≤ θ := by rw [div_le_iff₀ hL'] at hx0; linarith
  have hθ1 : θ ≤ 1 := by rw [le_div_iff₀ hL'] at hx1; linarith
  have hxθ : x = ((k : ℝ) + θ) / L := by rw [hθ]; field_simp; ring
  simp only [cellLinOK, Bool.and_eq_true] at hc
  obtain ⟨Y0, Y1, h0, h1, hle⟩ := sum_sound hok hL D α hw hθ0 hθ1 n
  have a0 := le_of_hiLe h0 hc.1
  have a1 := le_of_hiLe h1 hc.2
  rw [hxθ]
  nlinarith

lemma list_sum_range (f : ℕ → ℚ) (n : ℕ) : ((List.range n).map f).sum = ∑ k ∈ range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-- Raw linear-majorant certificate data at the trace `az`. -/
structure CDataLin where
  az : ℕ
  L : ℕ
  s : ℕ
  K : ℕ
  X : ℕ
  tab : LTree
  cs : List ℚ
  lam : ℚ
  e0s : List ℚ
  e1s : List ℚ
  Elo : ℚ
  zlo : ℚ
  zhi : ℚ
  lwlo : ℚ
  lwhi : ℚ

namespace CDataLin

variable (d : CDataLin)

def c (j : ℕ) : ℚ := d.cs.getD j 0

def D (j : ℕ) : ℚ :=
  if j ≤ d.K then 2 * (d.c j - (if j = 0 then 0 else d.c (j - 1))) else if j = d.K + 1 then -1 / 2 else 1 / 2

def α (j : ℕ) : ℤ := if j ≤ d.K then ((j * d.s : ℕ) : ℤ) else if j = d.K + 1 then -(d.L : ℤ) else (d.L : ℤ)

/-- The enclosure of `log z` used in the cell checks. -/
def lw : IV := ival d.lwlo d.lwhi

def e0 (k : ℕ) : ℚ := d.e0s.getD k 0

def e1 (k : ℕ) : ℚ := d.e1s.getD k 0

/-- The trapezoid charge of cell `k`. -/
def trapQ (k : ℕ) : ℚ := (max (d.e0 k - d.lam) 0 + max (d.e1 k - d.lam) 0) / 2

/-- **The certified exponent** `−E_lo + λ + (1/L) Σ_k ((e0 k − λ)₊ + (e1 k − λ)₊)/2`. -/
def PhiQ : ℚ := -d.Elo + d.lam + 1 / d.L * ((List.range (d.X * d.L)).map d.trapQ).sum

/-- The cell checks on `[lo, lo + n)`. -/
def cellsOK (lo n : ℕ) : Bool :=
  (List.range' lo n).all (fun k => cellLinOK d.tab d.L k d.D d.α d.lw (d.K + 3) (d.e0 k) (d.e1 k))

def EOK : Bool := (EIV d.tab d.s d.L d.c d.K).loGe d.Elo

/-- `[lwlo, lwhi]` contains the series enclosure of `log z`. -/
def lwOK : Bool := (lzRaw d.zlo d.zhi).loGe d.lwlo && (lzRaw d.zlo d.zhi).hiLe d.lwhi

def tailOK : Bool :=
  (d.lw.add (ofRat (1 / (d.X : ℚ)))).hiLt 0 &&
    ((((tabIV d.tab d.X).smul 2).sub (tabIV d.tab (d.X - 1))).add (d.lw.smul (d.X : ℚ))).hiLt d.lam

lemma cells_of (lo n : ℕ) (h : d.cellsOK lo n = true) (k : ℕ) (hk1 : lo ≤ k) (hk2 : k < lo + n) :
    cellLinOK d.tab d.L k d.D d.α d.lw (d.K + 3) (d.e0 k) (d.e1 k) = true := by
  unfold cellsOK at h
  rw [List.all_eq_true] at h
  exact h k (List.mem_range'_1.mpr ⟨hk1, hk2⟩)

/-- All cells from chunks `[n i, n i + n)`, `i < m`. -/
lemma cells_of_chunks (n m : ℕ) (h : ∀ i < m, d.cellsOK (n * i) n = true) (hX : d.X * d.L ≤ n * m) :
    ∀ k < d.X * d.L, cellLinOK d.tab d.L k d.D d.α d.lw (d.K + 3) (d.e0 k) (d.e1 k) = true := by
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
  az1 : 1 ≤ d.az
  L1 : 1 ≤ d.L
  X4 : 4 ≤ d.X
  Ks : d.K * d.s ≤ 2 * d.L
  len : d.cs.length = d.K
  crange : ∀ v ∈ d.cs, 0 ≤ v ∧ v ≤ 1
  mass : d.cs.sum * d.s = d.L
  zlo0 : 0 < d.zlo
  zlo5 : (2 * d.zlo + d.az) ^ 2 ≤ (d.az : ℚ) ^ 2 + 4
  zhi2 : 0 ≤ 2 * d.zhi + d.az
  zhi5 : (d.az : ℚ) ^ 2 + 4 ≤ (2 * d.zhi + d.az) ^ 2
  lw : d.lwOK = true
  tab : checkTab d.tab = true
  cells : ∀ k < d.X * d.L, cellLinOK d.tab d.L k d.D d.α d.lw (d.K + 3) (d.e0 k) (d.e1 k) = true
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

/-- The `Fact (1 ≤ az)` of valid data. -/
lemma fact (hv : d.Valid) : Fact (1 ≤ d.az) := ⟨hv.az1⟩

lemma mem_lw (hv : d.Valid) : @IV.mem d.lw (Real.log (zU d.az)) := by
  have := fact hv
  have h0 : (0 : ℚ) ≤ 2 * d.zlo + d.az := by have := hv.zlo0; positivity
  have hm := mem_lzRaw_az hv.zlo0 (zlo_le_az h0 hv.zlo5) (le_zhi_az hv.zhi2 hv.zhi5)
  have h := hv.lw
  simp only [lwOK, Bool.and_eq_true] at h
  exact ⟨ge_of_loGe hm h.1, le_of_hiLe hm h.2⟩

/-- `2U + v` as a sum of `ψ`-terms. -/
lemma F_eq (hv : d.Valid) (x : ℝ) :
    2 * (μ hv).U x + @vU d.az (fact hv) x =
      ∑ j ∈ range (d.K + 3), (d.D j : ℝ) * psiF (x - (d.α j : ℝ) / d.L) + x * Real.log (zU d.az) := by
  have := fact hv
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

/-- **The `LinCertU` of checked data.** -/
noncomputable def toLin (hv : d.Valid) : @LinCertU d.az (fact hv) :=
  haveI := fact hv
  { μ := μ hv
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
    e0 := fun k => (d.e0 k : ℝ)
    e1 := fun k => (d.e1 k : ℝ)
    hL := hv.L1
    hX := hv.X4
    hF := by
      intro k hk x hx0 hx1
      have hL : 0 < d.L := by have := hv.L1; omega
      have := cellLinOK_sound hv.tab hL d.D d.α (mem_lw hv) (d.K + 3) (hv.cells k hk) hx0 hx1
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
      linarith }

/-- **The certified exponent.** -/
theorem PhiLin_le (hv : d.Valid) : @LinCertU.PhiLin d.az (fact hv) (toLin hv) ≤ (d.PhiQ : ℝ) := by
  have := fact hv
  have hE : (d.Elo : ℝ) ≤ (μ hv).E := by
    have hm := mem_EIV hv.tab d.s (by have := hv.L1; omega : 0 < d.L) d.c d.K
    exact ge_of_loGe hm hv.E
  have hσ : ∑ k ∈ range (d.X * d.L), (toLin hv).trap k =
      ((((List.range (d.X * d.L)).map d.trapQ).sum : ℚ) : ℝ) := by
    rw [list_sum_range, Rat.cast_sum]
    refine sum_congr rfl (fun k _ => ?_)
    unfold LinCertU.trap trapQ
    push_cast
    rfl
  unfold LinCertU.PhiLin PhiQ
  change -(μ hv).E + (d.lam : ℝ) + 1 / (d.L : ℝ) * ∑ k ∈ range (d.X * d.L), (toLin hv).trap k ≤ _
  rw [hσ]
  push_cast
  linarith

/-- **A `DualCertU` from checked data**, with exponent below any rational `t > PhiQ`. -/
theorem exists_dual_le (hv : d.Valid) {t : ℚ} (ht : d.PhiQ < t) :
    ∃ C : @DualCertU d.az (fact hv), @DualCertU.Phi d.az (fact hv) C ≤ (t : ℝ) := by
  have := fact hv
  have ht' : (0 : ℝ) < (t : ℝ) - d.PhiQ := by
    have : (d.PhiQ : ℝ) < t := by exact_mod_cast ht
    linarith
  obtain ⟨C, hC⟩ := (toLin hv).exists_dual ht'
  have := PhiLin_le hv
  exact ⟨C, by linarith⟩

end CDataLin

end Chi2U.Cert
