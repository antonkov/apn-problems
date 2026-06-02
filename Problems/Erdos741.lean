import Lib.Defs
import Lib.Answer

/-!
# Erdős Problem 741

*References:*
 - [erdosproblems.com/741](https://www.erdosproblems.com/741)
 - [Er94b] Erdős, Paul, Some problems in number theory, combinatorics and combinatorial geometry.
    Math. Pannon. (1994), 261-269.
-/

open scoped Pointwise
open Set

namespace Erdos741

/-- Let $A\subseteq \mathbb{N}$ be such that $A+A$ has positive density.
Can one always decompose $A=A_1\sqcup A_2$ such that $A_1+A_1$ and $A_2+A_2$
both have positive density?

Note that this is using a literal interpretation of "positive density".
-/
theorem erdos_741.parts.i : answer(sorry) ↔ ∀ A : Set ℕ, HasPosDensity (A + A) → ∃ A₁ A₂,
    A = A₁ ∪ A₂ ∧ Disjoint A₁ A₂ ∧ HasPosDensity (A₁ + A₁)
    ∧ HasPosDensity (A₂ + A₂) := by
  sorry

/--
Is there a basis $A$ of order $2$ such that if $A=A_1\sqcup A_2$ then $A_1+A_1$ and $A_2+A_2$
cannot both have bounded gaps?
 -/
theorem erdos_741.parts.ii : answer(sorry) ↔ ∃ A : Set ℕ, IsAddBasisOfOrder (A ∪ {0}) 2 ∧ ∀ A₁ A₂,
    A = A₁ ∪ A₂ → Disjoint A₁ A₂ → ¬ (IsSyndetic (A₁ + A₁) ∧ IsSyndetic (A₂ + A₂)) := by
  sorry

end Erdos741
