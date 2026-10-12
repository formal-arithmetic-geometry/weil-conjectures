/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module


public import WeilConjectures.SixFunctors.ProEtale.Comparison

/-!
# Comparison isomorphisms for pullbacks and direct images

For the comparison morphism `ν` from the pro-étale to the étale site, this file constructs the
comparison isomorphisms `ν_Y^* Rf_* ≅ Rf_* ν_X^*` (blueprint
`prop-weil-pbc-comparison-direct-image`) for `f` quasi-compact and quasi-separated and
`ν_{Y'}^* g^* ≅ Lg^* ν_Y^*` (blueprint `lem-weil-pbc-comparison-pullback`), and the induced
comparisons of the sources and targets of the étale and the pro-étale exchange maps of a square.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

namespace ProEtale

section Comparison

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable (f) in
/-- Blueprint `prop-weil-pbc-comparison-direct-image`: for `f` quasi-compact and
quasi-separated, the canonical isomorphism `ν_Y^* Rf_* ≅ Rf_* ν_X^*` on bounded below derived
categories, the base change morphism of right derived functors induced by the underived
comparison `ν_Y^* f_* ⟶ f_* ν_X^*`
(`AlgebraicGeometry.ProEtale.lowerStarComparisonUpperStarBaseChange`). -/
noncomputable def rightDerivedLowerStarComparisonPlusIso [QuasiCompact f] [QuasiSeparated f] :
    R+(Etale.lowerStar A f) ⋙ D+(ν^*(Y)[A]) ≅ D+(ν^*(X)[A]) ⋙ R+(ProEtale.lowerStar A f) :=
  have := isIso_lowerStarComparisonUpperStarBaseChange f A
  have : IsIso (Functor.rightDerivedFunctorPlusBaseChange
      (lowerStarComparisonUpperStarBaseChange f A)) :=
    Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
      (asIso (lowerStarComparisonUpperStarBaseChange f A))
      (fun I _ ↦ rightAcyclic_lowerStar_comparisonUpperStar_obj_of_injective A f I)
  asIso (Functor.rightDerivedFunctorPlusBaseChange (lowerStarComparisonUpperStarBaseChange f A))

variable (f) in
/-- The isomorphism `ν_Y^* Rf_* ≅ Rf_* ν_X^*` of
`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonPlusIso`, with the pro-étale direct
image the unbounded right derived functor, as functors `D⁺(X_ét) ⥤ D(Y_proét)`. -/
noncomputable def rightDerivedLowerStarComparisonIso' [QuasiCompact f] [QuasiSeparated f] :
    R+(Etale.lowerStar A f) ⋙ DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[A]) ≅
      DerivedCategory.Plus.ι ⋙ D(ν^*(X)[A]) ⋙ R(ProEtale.lowerStar A f) :=
  Functor.isoWhiskerLeft R+(Etale.lowerStar A f)
      (ν^*(Y)[A]).mapDerivedCategoryPlusCompatibility.symm ≪≫
    Functor.isoWhiskerRight (rightDerivedLowerStarComparisonPlusIso f A) DerivedCategory.Plus.ι ≪≫
    Functor.isoWhiskerLeft D+(ν^*(X)[A])
      (ProEtale.lowerStar A f).rightDerivedFunctorPlusCompatibility ≪≫
    Functor.isoWhiskerRight (ν^*(X)[A]).mapDerivedCategoryPlusCompatibility
      R(ProEtale.lowerStar A f)

end Comparison

variable (Λ : Type (u + 1)) [CommRing Λ]

variable (g) in
/-- Blueprint `lem-weil-pbc-comparison-pullback`: the canonical isomorphism
`ν_{Y'}^* g^* ≅ Lg^* ν_Y^*`, as functors `D⁺(Y_ét) ⥤ D(Y'_proét)`. It is induced by the
underived isomorphism `AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso`, the
derived pullback of the exact functor `g^*` being computed degreewise. -/
noncomputable def leftDerivedUpperStarComparisonIso :
    D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g) ⋙ DerivedCategory.Plus.ι ⋙
        D(ν^*(Y')[ModuleCat.{u + 1} Λ]) ≅
      DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[ModuleCat.{u + 1} Λ]) ⋙
        L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g) :=
  Functor.isoWhiskerRight
      (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusCompatibility
      D(ν^*(Y')[ModuleCat.{u + 1} Λ]) ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm ≪≫
        Functor.mapDerivedCategoryCompIso _ _) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[ModuleCat.{u + 1} Λ]))
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).symm

variable (f g) in
/-- The comparison `ν_{Y'}^* g^* Rf_* ≅ Lg^* Rf_* ν_X^*` of the sources of the étale and the
pro-étale exchange maps, as functors `D⁺(X_ét) ⥤ D(Y'_proét)`. -/
noncomputable def baseChangeSourceComparisonIso [QuasiCompact f] [QuasiSeparated f] :
    (R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f) ⋙ D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g)) ⋙
        DerivedCategory.Plus.ι ⋙ D(ν^*(Y')[ModuleCat.{u + 1} Λ]) ≅
      DerivedCategory.Plus.ι ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ]) ⋙
        R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f) ⋙
          L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g) :=
  Functor.isoWhiskerLeft R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f)
      (leftDerivedUpperStarComparisonIso g Λ) ≪≫
    Functor.isoWhiskerRight (rightDerivedLowerStarComparisonIso' f (ModuleCat.{u + 1} Λ))
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g)

variable (g' f') in
/-- The comparison `ν_{Y'}^* Rf'_* g'^* ≅ Rf'_* Lg'^* ν_X^*` of the targets of the étale and the
pro-étale exchange maps, as functors `D⁺(X_ét) ⥤ D(Y'_proét)`. -/
noncomputable def baseChangeTargetComparisonIso [QuasiCompact f'] [QuasiSeparated f'] :
    (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g') ⋙ R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f')) ⋙
        DerivedCategory.Plus.ι ⋙ D(ν^*(Y')[ModuleCat.{u + 1} Λ]) ≅
      DerivedCategory.Plus.ι ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ]) ⋙
        L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g') ⋙
          R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f') :=
  Functor.isoWhiskerLeft D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g')
      (rightDerivedLowerStarComparisonIso' f' (ModuleCat.{u + 1} Λ)) ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarComparisonIso g' Λ)
      R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f')

end ProEtale

end AlgebraicGeometry
