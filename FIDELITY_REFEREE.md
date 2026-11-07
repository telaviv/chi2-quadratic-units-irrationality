# Statement-fidelity referee report: lean_chi2u

> **Note added for publication.** This report is kept as written, for the project under its development name
> `lean_chi2u`. It was written before the full `leanchecker` replay: all 62 modules have since been replayed and pass
> (see TRUST.md and `scripts/leanchecker.log`), which settles the "Limitation" in §2 and note 1. `STATUS.md` and the
> referee's scratch file are development files that are not in this repository. Note 2 (docstring names in
> `Statement.lean`) was fixed after the report.

Date: 2026-11-07. Referee: Claude (AI), acting as an independent statement-fidelity referee. I did not edit any Lean or
project file; this report is the only file I wrote. Scope: do the headline theorems say what the project claims? The
proofs themselves were not reviewed.

**Verdict: FAITHFUL.** The three headline statements mean exactly what README/TRUST claim. I found no hypotheses, no
shadowed names, no custom axioms and no compiler trust that weakens them. Two minor documentation notes are at the end.

## 1. Definitions traced to Mathlib

Elaborated statements, printed by `#check` / `#print` against the built project:

```
Chi2U.chi2_sqrt5_sub_two_irrational : Chi2U.TheoremU
Chi2U.golden_irrational' : Irrational (π ^ 2 - 18 * log goldenRatio ^ 2)
Chi2U.chi2_sqrt5_sub_two_eq : Chi2U.chi2 (√5 - 2) = π ^ 2 / 24 - 3 / 4 * log goldenRatio ^ 2
def Chi2U.TheoremU : Prop := Irrational (Chi2U.chi2 (√5 - 2))
def Chi2U.chi2 : ℝ → ℝ := fun z => ∑' (n : ℕ), Chi2U.chi2Term z n
def Chi2U.chi2Term : ℝ → ℕ → ℝ := fun z n => z ^ (2 * n + 1) / (2 * ↑n + 1) ^ 2
def Irrational : ℝ → Prop := fun x => x ∉ Set.range Rat.cast
```

* **χ₂** (`Chi2U/Defs.lean`): `chi2Term z n = z^(2n+1)/(2n+1)²` with `n : ℕ` cast to ℝ in the denominator, and
  `chi2 z = ∑' n, chi2Term z n`. This is the intended series Σ_{k≥0} x^{2k+1}/(2k+1)². The exponent `2*n+1` is a natural
  number (`Monoid.npow`), so there is no `rpow` issue.
* **Summability / junk value.** `tsum` returns 0 on a non-summable family. `summable_chi2Term : |z| ≤ 1 → Summable
  (chi2Term z)` is proved in the same file, and |√5 − 2| ≈ 0.236 ≤ 1. In my check file I proved
  `Summable (Chi2U.chi2Term (Real.sqrt 5 - 2))` from it (see §2), so `chi2 (√5 − 2)` is the actual sum of the series.
  Independently, `chi2_sqrt5_sub_two_eq` pins the value to π²/24 − ¾log²φ ≈ 0.2376 ≠ 0, which also rules out the junk
  value.
* **√5 − 2** is `Real.sqrt 5 - 2 : ℝ` (forced by `chi2 : ℝ → ℝ`; the `√` shown is Mathlib's prefix notation for
  `Real.sqrt`).
* **goldenRatio** resolves to Mathlib's `Real.goldenRatio`, an `abbrev` for `(1 + √5)/2`
  (`Mathlib/NumberTheory/Real/GoldenRatio.lean`). The project defines no `goldenRatio`, `pi`, `log`, `sqrt`,
  `Irrational` or `Real` of its own (grep of `Chi2U/`). `π` is `Real.pi` and `log` is `Real.log` (under `open Real`).
* **Irrational** is Mathlib's (`Mathlib/NumberTheory/Real/Irrational.lean`).
* **Hypotheses.** None. The three theorems have no arguments, and no `variable` appears in `Defs`, `Statement`, `Main`
  or `Golden/*`. `TheoremU` is a closed `Prop`.

Definitional checks in my own file (all accepted by Lean):

```lean
example : Chi2U.TheoremU ↔
    Irrational (∑' n : ℕ, (Real.sqrt 5 - 2) ^ (2 * n + 1) / (2 * (n : ℝ) + 1) ^ 2) := Iff.rfl
example : Irrational (Real.pi ^ 2 - 18 * Real.log ((1 + Real.sqrt 5) / 2) ^ 2) := Chi2U.golden_irrational'
example : (∑' n : ℕ, (Real.sqrt 5 - 2) ^ (2 * n + 1) / (2 * (n : ℝ) + 1) ^ 2)
    = Real.pi ^ 2 / 24 - 3 / 4 * Real.log ((1 + Real.sqrt 5) / 2) ^ 2 := Chi2U.chi2_sqrt5_sub_two_eq
example : Summable (Chi2U.chi2Term (Real.sqrt 5 - 2)) := ...  -- via summable_chi2Term and 2 < √5 < 3
```

So the statements, written only with Mathlib primitives, are: Σ (√5−2)^{2n+1}/(2n+1)² ∉ ℚ;
π² − 18·log²((1+√5)/2) ∉ ℚ; and Σ (√5−2)^{2n+1}/(2n+1)² = π²/24 − ¾·log²((1+√5)/2).

### Static scan of everything imported

* `Chi2U.lean` (the root module) imports all 62 `Chi2U.*` modules. External imports are only `Mathlib` and
  `Batteries.Tactic.Lemma`. `attic/` is not imported anywhere and is not part of the `lean_lib` (the lakefile's default
  globs cover only `Chi2U` and `Chi2U.*`).
* No `sorry`, `admit`, `axiom` declaration, `native_decide`, `implemented_by`, `@[extern]`, `unsafe`, `opaque`,
  `macro`, `macro_rules`, `elab`, `syntax`, `notation` declaration, `@[csimp]`, `debug.*` option, `ofReduceBool` or
  `attribute [-instance]` in `Chi2U/` or `Chi2U.lean`. (The grep hits on "notation" and "syntax" are comments or the
  Apache LICENSE text.)
* `set_option`s used: `backward.isDefEq.respectTransparency false` (9×, ported PNT `Wiener.lean`),
  `lang.lemmaCmd`, `maxRecDepth`, linter options. These affect elaboration only, not kernel checking.
* Instances: `Fact (¬ IsSquare (5 : ℚ))` (proved from `not_isSquare_five`), maximal-ideal and `CharP` instances in
  `NonVan/ModL.lean` (proved), and instances on the PNT port's own types (`CS`, `W1`, `trunc`), plus
  `MeasurableSpace`/`BorelSpace Circle` and two `local` coercions. All are definitions or proved facts. None touches ℝ,
  `Real.sqrt`, `Real.log`, `tsum` or `Irrational`, so none can change the meaning of the headline statements.
* `Decidable`: the certificate uses `decide +kernel` (kernel evaluation, no compiler trust). It contributes no axioms
  beyond the standard three, as `#print axioms` confirms.

## 2. Axiom check (re-run)

`lake build --no-build`: "All targets up-to-date (9110 jobs)", so the checks below ran against the current sources.

`lake env lean Axioms.lean` (4 m 27 s): all 22 listed declarations, including the four headline ones, print
`[propext, Classical.choice, Quot.sound]`.

My own file (`RefCheck.lean` in my scratchpad: the `#check`s, the definitional `example`s and the summability proof
above, then `#print axioms`) gave:

```
'Chi2U.chi2_sqrt5_sub_two_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2U.golden_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2U.golden_irrational'' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2U.chi2_sqrt5_sub_two_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2U.summable_chi2Term' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### leanchecker replay

`leanchecker.exe` ships with the toolchain (`~/.elan/toolchains/leanprover--lean4---v4.35.0/bin/`); nothing was
installed. I replayed with `lake env leanchecker <module>`. Each run replays that module's own declarations against its
compiled imports.

| module | result | time |
|---|---|---|
| Chi2U.Defs | pass (rc 0, no output) | 118 s (cold Mathlib load) |
| Chi2U.Statement | pass | 34 s |
| Chi2U.Main | pass | 32 s |
| Chi2U.Golden.ClosedForm | pass | 35 s |
| Chi2U.Golden.Corollary | pass | 32 s |
| Chi2U.Golden.Landen | pass | 32 s |
| Chi2U.Golden.Dilog | pass | 32 s |
| Chi2U.MainCond | pass | 31 s |
| Chi2U.Criterion | pass | 32 s |

Negative control: `lake env leanchecker Chi2U.NoSuchModule` exits with rc 1 ("Could not find any oleans"), so rc 0
means something was actually loaded.

**Limitation.** This covers the statement modules and the whole golden-ratio chain. It does not cover the other 53
modules: Arith, Analytic, Cert (including the 6.5-minute `decide +kernel` certificate), NonVan, PNT and the rest. For
those, the only kernel check is the one `lake build` did. A full replay in lean_chi2's style (a loop over all modules,
about 2 h) is still owed, as STATUS.md says. `--fresh` (re-checking Mathlib too) was not run.

## 3. Numerical sanity [Numerical]

mpmath at 70 digits:

```
χ₂(√5−2) (series)          = 0.2375599012791608147454069882378567272924327127647254563
π²/24 − ¾ log²φ            = 0.2375599012791608147454069882378567272924327127647254563
½(Li₂(√5−2) − Li₂(2−√5))   = 0.2375599012791608147454069882378567272924327127647254563
difference                 = 4.5e−72
π² − 18 log²φ = 24·χ₂(√5−2) = 5.701437630699859553889767717708561455018385106353410952
```

The formal identity is a true identity, and the corollary's factor of 24 is right. The constant matches PROOF_U.md's
headline ("T = π²/24 − ¾·log²φ = χ₂(√5 − 2) ∉ ℚ; equivalently π² − 18 log²φ ∉ ℚ").

## 4. Comparison with lean_chi2

`diff lean_chi2/Chi2Irrational/Defs.lean lean_chi2u/Chi2U/Defs.lean` differs only in the namespace lines
(`Chi2Irr` → `Chi2U`), and the same holds for `Criterion.lean`. So χ₂ is defined identically in both projects, with
the same series and the same summability lemma. The statement shapes match: lean_chi2 has
`Chi2OneThirdIrrational : Prop := Irrational (chi2 (1 / 3))` (and `1/5`); lean_chi2u has
`TheoremU : Prop := Irrational (chi2 (Real.sqrt 5 - 2))`. The only difference is the argument, an irrational real
(`Real.sqrt 5 - 2`) instead of the rational literal `1/3` coerced to ℝ. That needs no extra care: `Real.sqrt 5` is the
genuine square root of 5, since `Real.sqrt` of a nonnegative argument is not a junk value. lean_chi2u also adds the
proved closed form, which lean_chi2 does not have.

## Notes (not defects of the statements)

1. TRUST.md correctly says the leanchecker replay "has not been run". After this report, 9 of the 62 modules have been
   replayed (above); the full replay is still open.
2. The docstring in `Statement.lean` cites `Golden.ClosedForm.chi2_sqrt5_sub_two_eq` and
   `Golden.Corollary.golden_irrational'`, but the actual names are `Chi2U.chi2_sqrt5_sub_two_eq` and
   `Chi2U.golden_irrational'` (file paths, not namespaces). This is cosmetic only.
