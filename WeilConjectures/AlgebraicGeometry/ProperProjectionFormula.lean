/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-!
# The proper projection formula with the base factor first

The map is the specified composite of the canonical signed derived symmetry, the
adjoint-of-counit projection map, and direct image of the signed symmetry on the source.
The derived inverse image is the exact termwise inverse image through
`leftDerivedUpperStarIsoMapDerivedCategory`; no boundedness condition is imposed.

## References

* [Stacks, Tag 0F0G], [Stacks, Tag 06YU]
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The proper projection formula for ordinary unbounded small-etale module complexes, with
finite commutative coefficients and the tensor factors reordered with the base factor first.
(Stacks, Tag 0F0G) -/
theorem isIso_proper_projection_formula_reordered
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T : Scheme.{u}} (r : V ⟶ T) [IsProper r]
    [IsLocallyNoetherian V] [CompactSpace V] [IsLocallyNoetherian T] [CompactSpace T]
    (L : DerivedCategoryModule A V) (K : DerivedCategoryModule A T) :
    IsIso (
      ((derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app K).app
          ((lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctor.obj L) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) r).app L).app K ≫
        (lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctor.map
          (((derivedTensorSymmetry (ModuleCat.{u + 1} A) V).hom.app L).app
            ((upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor.obj K))) := by
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite A r
  infer_instance

end AlgebraicGeometry.Etale
