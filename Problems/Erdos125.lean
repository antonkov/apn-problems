import Lib.Defs
import Lib.Answer

/-!
# Erdős Problem 125

*Reference:* [erdosproblems.com/125](https://www.erdosproblems.com/125)
-/

open Nat Pointwise

namespace Erdos125

set_option quotPrecheck false

/--
A set `A` is the set of integers which have only the digits $0, 1$ when written base 3,
-/
local notation "A" => { x : ℕ | (digits 3 x).toFinset ⊆ {0, 1} }
/--
and $B$ is the set of integers which have only the digits $0, 1$ when written base 4.
-/
local notation "B" => { x : ℕ | (digits 4 x).toFinset ⊆ {0, 1} }

/--
Does $A + B$ have positive lower density?
-/
theorem erdos_125.variants.positive_lower_density :
    answer(sorry) ↔ 0 < (A + B).lowerDensity := by
  sorry

end Erdos125
