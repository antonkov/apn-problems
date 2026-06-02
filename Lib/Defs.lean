import Mathlib

/-!
# Definitions for problem statements
-/

open Filter Set
open scoped Pointwise Topology

/-! ## Density -/

namespace Set

/-- Partial density of `S` relative to `A` at `b`. -/
@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

/-- Upper density of `S` relative to `A`. -/
noncomputable def upperDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.limsup fun (b : β) ↦ S.partialDensity A b

/-- Lower density of `S` relative to `A`. -/
noncomputable def lowerDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.liminf fun (b : β) ↦ S.partialDensity A b

/-- `S` has density `α` relative to `A`. -/
def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

/-- `S` has positive density relative to `A`. -/
def HasPosDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : Prop :=
  ∃ α > 0, S.HasDensity α A

end Set

/-! ## Syndetic sets -/

/-- A set of natural numbers has bounded gaps. -/
def IsSyndetic (A : Set ℕ) : Prop := ∃ p, ∀ n, (A ∩ .Icc n (n + p)).Nonempty

/-! ## Sidon sets -/

/-- A Sidon set: all pairwise sums are distinct (up to commutativity). -/
def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

/-! ## Additive basis -/

namespace Set
variable {M : Type*} [CommMonoid M] {A : Set M} {n : ℕ}

/-- A set `A : Set M` is a multiplicative basis of order `n` if any element
can be expressed as a product of `n` elements lying in `A`. -/
@[to_additive
/-- A set `A : Set M` is an additive basis of order `n` if any element
can be expressed as a sum of `n` elements lying in `A`. -/]
def IsMulBasisOfOrder (A : Set M) (n : ℕ) : Prop := ∀ a, a ∈ A ^ n

end Set

export Set (IsAddBasisOfOrder)

/-! ## Arithmetic progressions -/

namespace Set
variable {α : Type*} [AddCommMonoid α]

/-- `s` is an arithmetic progression of length `l` with first term `a` and difference `d`. -/
def IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

/-- `s` is an arithmetic progression of length `l`. -/
def IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

end Set

/-- A coloring contains a monochromatic AP of length `k`. -/
def ContainsMonoAPofLength {α : Type*} [AddCommMonoid α] {κ : Type} [Finite κ] {M : Set α}
    (coloring : M → κ) (k : ℕ) : Prop :=
  ∃ c : κ, ∃ ap : Set M, ((·.1) '' ap).IsAPOfLength k ∧
    ∀ m ∈ ap, coloring m = c

/-! ## Geometry -/

namespace EuclideanGeometry

scoped notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

end EuclideanGeometry

open EuclideanGeometry

namespace Set

/-- `s.Triplewise r` means `r x y z` for all distinct `x y z ∈ s`. -/
protected def Triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z

end Set

/-- A set of points is non-trilinear if no three are collinear. -/
def NonTrilinear {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (A : Set P) : Prop :=
  A.Triplewise (fun x y z ↦ ¬ Collinear ℝ {x, y, z})
