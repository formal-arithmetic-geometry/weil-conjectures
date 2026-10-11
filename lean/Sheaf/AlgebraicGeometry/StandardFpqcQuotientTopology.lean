import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- Standard finite affine fpqc covers detect openness.
Source: Stacks Project, Morphisms, Tag 02JY
(blueprint: lem-weil-pbc-standard-fpqc-quotient-topology).

Proof: Package the finite family as the spectrum of the product ring, apply the
quotient-topology theorem for flat quasi-compact surjective morphisms, and use
that the coproduct summands are open and cover the product spectrum. -/
theorem standard_fpqc_quotient_topology
    (R : Type u) [CommRing R]
    (J : Type v) [Finite J]
    (A : J → Type u) [∀ j, CommRing (A j)] [∀ j, Algebra R (A j)]
    [Module.FaithfullyFlat R (∀ j, A j)]
    (W : Set (Spec (CommRingCat.of R)))
    (hW : ∀ j : J,
      IsOpen ((Spec.map (CommRingCat.ofHom (algebraMap R (A j)))) ⁻¹' W)) :
    IsOpen W := by
  sorry

end AlgebraicGeometry
