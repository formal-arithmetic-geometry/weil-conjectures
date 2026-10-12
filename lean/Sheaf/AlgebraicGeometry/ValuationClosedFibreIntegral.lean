module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.Modules.Invertible

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry.Scheme.Modules

/-- The integral quotient fibre over the residue field identifies with the closed fibre.
Source: Stacks Project, More on Morphisms, Tag 0EX8.
(blueprint: new-valuation-closed-fibre-integral)
-/
theorem closed_fibre_is_integral
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (hX₀ : IsIntegral (Limits.pullback f (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))))) :
    IsIntegral (f.fiber (IsLocalRing.closedPoint A)) := by sorry

end AlgebraicGeometry.Scheme.Modules
