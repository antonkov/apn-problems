import Lib.Defs
import Lib.Answer

/-!
# Erdős Problem 26

*References:*
- [erdosproblems.com/26](https://www.erdosproblems.com/26)
- [Te19](https://arxiv.org/pdf/1908.00488) G. Tenenbaum,
  _Some of Erdős' unconventional problems in number theory, thirty-four years later_,
  arXiv:1908.00488 [math.NT] (2019)
-/

namespace Erdos26

open Filter Set
open scoped Topology

/-- A sequence of naturals $(a_i)$ is _thick_ if their sum of reciprocals diverges:
$$
  \sum_i \frac{1}{a_i} = \infty
$$-/
def IsThick {ι : Type*} (A : ι → ℕ) : Prop := ¬Summable (fun i ↦ (1 : ℝ) / A i)

/-- The set of multiples of a sequence $(a_i)$ is $\{na_i | n \in \mathbb{N}, i\}$. -/
def MultiplesOf {ι : Type*} (A : ι → ℕ) : Set ℕ := Set.range fun (n, i) ↦ n * A i

/-- A sequence of naturals $(a_i)$ is _weakly Behrend_ with respect to $\varepsilon \in \mathbb{R}$
if at least $1 - \varepsilon$ density of all numbers are a multiple of $A$. -/
def IsWeaklyBehrend {ι : Type*} (A : ι → ℕ) (ε : ℝ) : Prop := 1 - ε ≤ (MultiplesOf A).lowerDensity

/--
Tenenbaum asked the weaker variant where for every $\epsilon>0$ there is
some $k=k(\epsilon)$ such that at least $1-\epsilon$ density of all integers have a
divisor of the form $a+k$ for some $a\in A$.
-/
theorem erdos_26.variants.tenenbaum : answer(sorry) ↔ ∀ᵉ (A : ℕ → ℕ), StrictMono A → IsThick A →
    (∀ ε > (0 : ℝ), ∃ k, IsWeaklyBehrend (A · + k) ε) := by
  sorry

end Erdos26
