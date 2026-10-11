import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.Topology.Irreducible

universe u v

open scoped BigOperators
namespace AlgebraicGeometry

/-!
# Dimension at a point from irreducible components

Source: Stacks Project, Algebra, Lemma Tag 00OT
(blueprint: lem-weil-pbc-dimension-at-point-components).
-/

/-- Source: Stacks Project, Algebra, Lemma Tag 00OT
(blueprint: lem-weil-pbc-dimension-at-point-components).
The local Krull dimension of a finite type affine scheme over a field is the maximum of the
 dimensions of the irreducible components through the point, equivalently the maximum of the
 dimensions of the quotients by the minimal primes contained in the point, and is the minimum of
 the dimensions of the localizations at maximal ideals above the point.

Proof (Stacks 00OT): the components of `Spec S` are the `V(q_j)` for the finitely many minimal
primes, and `dim V(q_j) = dim S/q_j`; chains through `S/q_j` (00OS) give `dim S_m ≥ N` for every
maximal `m ⊇ p`, where `N = max dim S/q_i` over the minimal primes `q_i ⊆ p`; every open
neighbourhood of `p` contains a maximal ideal over `p` (Jacobson), so every neighbourhood has
dimension `≥ N`; the open `U` obtained by removing the components not through `x` has dimension
`≤ N`, so `dim_x X = N`, and a maximal `m₀ ⊇ p` in `U` has `dim S_{m₀} = N`. -/
theorem dimension_at_point_components
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : Ideal S) [p.IsPrime] :
    let X := Spec (CommRingCat.of S)
    let x : X := ⟨p, inferInstance⟩
    ∃ qs : Finset (Ideal S),
      (∀ q : Ideal S, q ∈ qs ↔ q.IsPrime ∧ q ≤ p ∧
        ∀ r : Ideal S, r.IsPrime → r ≤ q → r = q) ∧
      qs.Nonempty ∧
      ∃ n : ℕ,
        topologicalKrullDimAt x = n ∧
        (∀ Z : Set X, Z ∈ irreducibleComponents X → x ∈ Z →
          topologicalKrullDim Z ≤ n) ∧
        (∃ Z : Set X, Z ∈ irreducibleComponents X ∧ x ∈ Z ∧
          topologicalKrullDim Z = n) ∧
        (∀ q ∈ qs, ringKrullDim (S ⧸ q) ≤ n) ∧
        (∃ q ∈ qs, ringKrullDim (S ⧸ q) = n) ∧
        (∀ (m : Ideal S) [m.IsMaximal], p ≤ m →
          (n : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime m)) ∧
        (∃ (m : Ideal S) (_ : m.IsMaximal), p ≤ m ∧
          ringKrullDim (Localization.AtPrime m) = n)
    := by
  sorry

end AlgebraicGeometry
