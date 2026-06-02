import Lib.Defs
import Lib.Answer

/-!
# Erdős Problem 138

*References:*
- [erdosproblems.com/138](https://www.erdosproblems.com/138)
- [Er81] Erdős, P., On the combinatorial problems which I would most like to see solved.
  Combinatorica (1981), 25-42.
-/

open Nat Filter
open scoped BigOperators

namespace Erdos138

/--
The set of natural numbers that guarantee a monochromatic arithmetic progression.

A number `N` belongs to this set if, for a given number of colors `r` and an arithmetic
progression length `k`, any `r`-coloring of the integers `{1, ..., N}` must contain a
monochromatic arithmetic progression of length `k`.
-/
def monoAP_guarantee_set (r k : ℕ) : Set ℕ :=
  { N | ∀ coloring : Finset.Icc 1 N → Fin r, ContainsMonoAPofLength coloring k}

/--
The **van der Waerden number**, is the smallest integer `N` such that any `r`-coloring of
`{1, ..., N}` is guaranteed to contain a monochromatic arithmetic progression of
length `k`. It is defined as the infimum of the (non-empty) set of all such numbers `N`.
-/
noncomputable def monoAPNumber (r k : ℕ) : ℕ := sInf (monoAP_guarantee_set r k)

/--
An abbreviation for the van der Waerden number for 2 colors, commonly written as `W(k)`.
This represents the smallest integer `N` such that any 2-coloring of `{1, ..., N}`
must contain a monochromatic arithmetic progression of length `k`.
-/
noncomputable abbrev W : ℕ → ℕ := monoAPNumber 2

/--
In [Er81] Erdős asks whether $W(k+1) - W(k) \to \infty$.
-/
theorem erdos_138.variants.difference :
    answer(sorry) ↔ atTop.Tendsto (fun k => (W (k + 1) - W k)) atTop := by
  sorry

end Erdos138
