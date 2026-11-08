/-
# Lemma 10′: definitions of the rescaled anchored basis and the entries `G_{ij}` (PROOF_U §4)

Moved verbatim out of `Arith/TwoAdic.lean` (which imports this file through `TwoAdicEntries`), so that the helper
files can use them. Rescale `τ = t/2`: poles `ξ_k = k − J`; anchored basis `a_i = Π_{l<i}(τ − ξ_l)`,
`b_j = Π_{l<j}(τ − ξ_{K−1−l})`; `G_{ij} = Λ̃_X(a_i b_j) = 2^{K+1} Λ_X((a_i b_j)(t/2))`, `K = h + 1`.
-/
import Chi2U.Arith.VGe

namespace Chi2U

open Polynomial Finset

/-- The rescaled poles `ξ_k = k − J`. -/
def xiPole (h k : ℕ) : ℚ := (k : ℚ) - ((h / 2 : ℕ) : ℚ)

/-- `a_i = Π_{l<i} (τ − ξ_l)`. -/
noncomputable def aAnch (h i : ℕ) : ℚ[X] := ∏ l ∈ range i, (X - C (xiPole h l))

/-- `b_j = Π_{l<j} (τ − ξ_{K−1−l})`. -/
noncomputable def bAnch (h j : ℕ) : ℚ[X] := ∏ l ∈ range j, (X - C (xiPole h (h - l)))

/-- `A`-part of `G_{ij} = Λ̃_X(a_i b_j) = 2^{K+1} Λ_X((a_i b_j)(t/2))`. -/
noncomputable def GA (h i j : ℕ) : Q5 := 2 ^ (h + 2) * Afun 2 h ((aAnch h i * bAnch h j).comp (C (1 / 2) * X))

/-- `B`-part of `G_{ij}`. -/
noncomputable def GB (h i j : ℕ) : Q5 := 2 ^ (h + 2) * Bfun 2 h ((aAnch h i * bAnch h j).comp (C (1 / 2) * X))

end Chi2U
