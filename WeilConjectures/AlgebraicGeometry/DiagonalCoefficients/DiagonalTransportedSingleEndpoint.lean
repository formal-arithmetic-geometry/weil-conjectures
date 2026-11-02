/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalSupportedEndpointTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalChernCoefficientPullback

/-! # Exact single normalization of a transported endpoint -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Functor.mapDerivedCategory

/-- Transport through exact realization commutes with placing an ordinary endpoint
in degree zero.

Source: blueprint latest, diagonal coefficient changes (3), supported endpoint
transport through exact realization.
(blueprint: lem-diagonal-transported-single-endpoint).

Proof: apply the faithful derived realization and postcompose with the realized
target endpoint. The transported map has its defining preimage normalization.
For the single of the ordinary transport, naturality of the exact single
comparison and compatibility of the localized square with single objects reduce
its normalization to the ordinary preimage normalization. Cancel the realized
target isomorphism. -/
theorem diagonalTransportedSingleEndpoint
    {A B C D : Type*}
    [Category A] [Abelian A] [Category B] [Abelian B]
    [Category C] [Abelian C] [Category D] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (P : A ⥤ B) (F : A ⥤ C) (F' : B ⥤ D) (V : C ⥤ D)
    [P.Additive] [F.Additive] [F'.Additive] [V.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [F'.Full] [F'.Faithful]
    [F'.mapDerivedCategory.Full] [F'.mapDerivedCategory.Faithful]
    (e : P ⋙ F' ≅ F ⋙ V) {X : A} {X' : B} {Y : C} {Y' : D}
    (s : F.obj X ≅ Y) (s' : F'.obj X' ≅ Y') (b : V.obj Y ≅ Y') :
    diagonalTransportedEndpoint P.mapDerivedCategory F.mapDerivedCategory
        F'.mapDerivedCategory V.mapDerivedCategory
        (Functor.mapDerivedCategorySquareIso e)
        (diagonalRealizedSingleSource F s) (diagonalRealizedSingleSource F' s')
        ((V.mapDerivedCategorySingleFunctor 0).app Y ≪≫
          (DerivedCategory.singleFunctor D 0).mapIso b) =
      (P.mapDerivedCategorySingleFunctor 0).app X ≪≫
        (DerivedCategory.singleFunctor B 0).mapIso
          (diagonalTransportedEndpoint P F F' V e s s' b) := by
  let v := diagonalTransportedEndpoint P F F' V e s s' b
  have ho := diagonalTransportedEndpoint_normalization P F F' V e s s' b
  have hd := diagonalTransportedEndpoint_normalization P.mapDerivedCategory
    F.mapDerivedCategory F'.mapDerivedCategory V.mapDerivedCategory
    (Functor.mapDerivedCategorySquareIso e)
    (diagonalRealizedSingleSource F s) (diagonalRealizedSingleSource F' s')
    ((V.mapDerivedCategorySingleFunctor 0).app Y ≪≫
      (DerivedCategory.singleFunctor D 0).mapIso b)
  apply Iso.ext
  apply F'.mapDerivedCategory.map_injective
  apply (cancel_mono (diagonalRealizedSingleSource F' s').hom).mp
  rw [← hd]
  simp only [diagonalRealizedSingleSource, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  have hs := (V.mapDerivedCategorySingleFunctor 0).hom.naturality s.hom
  have hv := (F'.mapDerivedCategorySingleFunctor 0).hom.naturality v.hom
  dsimp only [Functor.comp_map] at hs hv
  have hsq := exactSquare_single P F' F V e X
  dsimp only [Functor.mapDerivedCategorySquareIso] at hsq
  rw [reassoc_of% hs]
  erw [reassoc_of% hsq, reassoc_of% hv]
  simp only [← (DerivedCategory.singleFunctor D 0).map_comp]
  rw [ho]

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
