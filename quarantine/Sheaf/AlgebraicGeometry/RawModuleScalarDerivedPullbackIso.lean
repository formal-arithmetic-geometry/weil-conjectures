/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison

/-! # Derived canonical scalar pullback comparison

Source: the derived exact-functor composition and natural-isomorphism comparisons.
(blueprint: def-sbc-raw-scalar-derived-pullback-iso).
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale.RawModuleScalarComparison

/-- Compose the derived exact-functor comparisons for scalar forgetting.
(blueprint: def-sbc-raw-scalar-derived-pullback-iso). -/
noncomputable def derivedPullbackIsoImpl (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus ⋙
        (forget Λ X).mapDerivedCategoryPlus ≅
      (forget Λ Y).mapDerivedCategoryPlus ⋙
        (upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso
    (upperStar (ModuleCat.{u + 1} Λ) f) (forget Λ X)).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (pullbackIso Λ f) ≪≫
      Functor.mapDerivedCategoryPlusCompIso
        (forget Λ Y) (upperStar AddCommGrpCat.{u + 1} f)

end AlgebraicGeometry.Etale.RawModuleScalarComparison
