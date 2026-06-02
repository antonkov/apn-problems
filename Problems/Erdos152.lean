import Lib.Defs
import Lib.Answer

/-!
# Erdős Problem 152

*References:*
 - [erdosproblems.com/152](https://www.erdosproblems.com/152)
 - [ESS94] Erdős, P. and Sárközy, A. and Sós, T., On Sum Sets of Sidon Sets, I. Journal of Number
    Theory (1994), 329-347.
-/

open scoped Pointwise Asymptotics
open Filter

namespace Erdos152

/-- Define `f n` to be the minimum of `|{s | s - 1 ∉ A + A, s ∈ A + A, s + 1 ∉ A + A}|` as `A`
ranges over all Sidon sets of size `n`. -/
noncomputable def f (n : ℕ) : ℕ :=
  ⨅ A : {A : Set ℕ | A.ncard = n ∧ IsSidon A},
  {s : ℕ | s - 1 ∉ A.1 + A.1 ∧ s ∈ A.1 + A.1 ∧ s + 1 ∉ A.1 + A.1}.ncard

/--
Must `lim f n = ∞`?
-/
theorem erdos_152 : answer(sorry) ↔ Tendsto f atTop atTop := by
  sorry

end Erdos152
