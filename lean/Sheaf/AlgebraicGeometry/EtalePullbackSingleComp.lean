/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs

/-! # Pullback composition on a sheaf in degree zero

Source: Stacks Tag 0D6D, composition of derived pullback; Tag 09Z1, restriction maps.
(blueprint: lem-sbc-pullback-single-comp)
-/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Composition of the degree-zero comparisons for two exact étale pullbacks.

Source: Stacks Tags 0D6D and 09Z1; the coefficient identity in the proof of
lem-sbc-pullback-comparison-comp, step 2.
(blueprint: lem-sbc-pullback-single-comp)

Proof: represent F[0] by the single cochain complex on F. The composition comparison
for the levelwise pullbacks is the underived pullback composition comparison in degree
zero; in every other degree its components are the unique maps of zero objects. The
single-complex comparison for each pullback is the identity at degree zero, and the
canonical zero-object comparison elsewhere. Hence the two routes agree degreewise.
Transport this equality through the homotopy quotient and the derived localization,
using the factorization isomorphisms defining mapDerivedCategoryCompIso and
mapDerivedCategorySingleFunctor. Their intermediate factors cancel by naturality.
The bounded-below comparisons are restrictions of these same isomorphisms along the
fully faithful inclusion D⁺ → D, which reflects equality. The inverse underived
composition comparison at the end gives exactly the displayed orientation. This
argument applies to identity morphisms and zero sheaves without extra assumptions.
-/
theorem Etale.upperStarPlusComp_single
    {T T₁ T₂ : Scheme.{u}} (π₁ : T₁ ⟶ T₂) (π₂ : T₂ ⟶ T)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    D+((π₁)^*[ModuleCat.{u + 1} Λ]).map
        ((((π₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F) ≫
      ((((π₁)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
        (((π₂)^*[ModuleCat.{u + 1} Λ]).obj F)) ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) π₁ π₂ (π₁ ≫ π₂) rfl).inv.app F) =
    (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) π₁ π₂).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      ((((π₁ ≫ π₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F) :=
  by sorry

end AlgebraicGeometry
