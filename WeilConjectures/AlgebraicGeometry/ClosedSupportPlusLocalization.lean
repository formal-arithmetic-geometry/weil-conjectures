/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

import WeilConjectures.AlgebraicGeometry.EtaleClosedSupportTriangle

/-! # Localization on the actual bounded below support adjunction

Source: Stacks Project, Tags 09XQ and 0A45.
(blueprint: lem-per-closed-support-plus-localization).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Etale

/-- The actual bounded below support counit and open unit form a localization triangle.
Its open term is right orthogonal to the closed image in every shift.

Source: Stacks Project, Tags 09XQ and 0A45; the bounded below restriction of
`exists_etale_closedSupportTriangle`.
(blueprint: lem-per-closed-support-plus-localization).

Proof: Closed direct image is exact. Derive its supported-kernel adjunction using
bounded below injective resolutions. Identify this right adjoint with the restriction
of the ambient closed right adjoint: if K has lower bound n, adjunction and exactness
of closed direct image give Hom(B, i!K) = 0 for B in degrees at most n-1. Thus i!K
has the same lower bound. Uniqueness of right adjoints identifies the restricted
adjunction with the specified derivedPlus adjunction, including its counit.
Restrict the ambient localization triangle along the fully faithful inclusion of D+;
the open direct image also preserves a lower bound. Transport its boundary along
the adjoint identification. For orthogonality, open inverse image kills closed
direct image, commutes with shifts, and is left adjoint to the open right derived
direct image. The adjunction therefore identifies the indicated Hom group with
maps from a zero object. This applies also to empty closed or open complements. -/
theorem closedSupportPlus_localization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    (∀ K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
      ∃ δ, Triangle.mk
        ((lowerStarClosedUpperShriekAdjunction
          (ModuleCat.{u + 1} A) i j hij).derivedPlus.counit.app K)
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).derivedPlus.unit.app K)
        δ ∈ distTriang _) ∧
    (∀ (M : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (N : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (n : ℤ),
      Subsingleton
        (((lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus.obj M)⟦n⟧ ⟶
          (lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorPlus.obj N)) := by sorry

end AlgebraicGeometry.Etale
