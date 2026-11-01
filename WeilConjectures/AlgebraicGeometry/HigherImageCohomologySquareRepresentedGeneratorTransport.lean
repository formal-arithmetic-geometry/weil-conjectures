/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.HigherImageCohomologySquareRawMap
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
/-- Naturality of the free-representable generator across inverse image.
This is the represented-generator step in the derived-mate calculation.
Source: Stacks Project, Tags 03CB and 03Q8.
(blueprint: lem-sf-higher-image-cohomology-square-represented-generator-transport). -/
theorem higherImageCohomologySquare_represented_generator_transport
    {S T : Scheme.{u}} (a : T ⟶ S) (U : S.Etale)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (x : (abelianComparisonFree T).obj (a.Etale.obj U) ⟶ G) :
    freeRepresentableHomEquiv T (a.Etale.obj U) G x =
      freeRepresentableHomEquiv S U (((a)_*[AddCommGrpCat.{u + 1}]).obj G)
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} a).homEquiv _ _
          ((abelianFreeRepresentablePullbackIso a U).hom ≫ x)) := by
  sorry
end AlgebraicGeometry.Etale
