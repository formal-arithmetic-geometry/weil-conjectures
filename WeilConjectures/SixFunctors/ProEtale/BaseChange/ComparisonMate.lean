/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange

/-!
# The comparison of direct images is the mate of the comparison of pullbacks

For a quasi-compact quasi-separated morphism `f : X ⟶ Y`, the comparison isomorphism
`ν_Y^* Rf_* ≅ Rf_* ν_X^*` (`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonIso'`) is
the mate, under the derived adjunctions `f^* ⊣ Rf_*` (étale, bounded below) and
`Lf^* ⊣ Rf_*` (pro-étale), of the inverse of the comparison isomorphism
`ν_X^* f^* ≅ Lf^* ν_Y^*` (`AlgebraicGeometry.ProEtale.leftDerivedUpperStarComparisonIso`).

The underived counterpart (`AlgebraicGeometry.ProEtale.lowerStarComparisonUpperStarBaseChange_eq`)
is formal: both underived comparisons are obtained by taking mates of the same isomorphism
`f_* ν_{X,*} ≅ ν_{Y,*} f_*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section Underived

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The underived base change morphism `ν_Y^* f_* ⟶ f_* ν_X^*` is the mate, under the
adjunctions `f^* ⊣ f_*` on the étale and on the pro-étale sites, of the comparison
`ν_Y^* ⋙ f^* ≅ f^* ⋙ ν_X^*` of pullbacks. -/
lemma lowerStarComparisonUpperStarBaseChange_eq :
    lowerStarComparisonUpperStarBaseChange f A =
      mateEquiv (Etale.upperStarLowerStarAdjunction A f)
        (ProEtale.upperStarLowerStarAdjunction A f)
        (comparisonUpperStarCompUpperStarIso A f).hom := by
  refine ((mateEquiv (comparisonAdjunction A X) (comparisonAdjunction A Y)).symm_apply_eq).2 ?_
  refine Eq.trans ?_ (iterated_mateEquiv_conjugateEquiv (Etale.upperStarLowerStarAdjunction A f)
    (ProEtale.upperStarLowerStarAdjunction A f) (comparisonAdjunction A Y)
    (comparisonAdjunction A X) (comparisonUpperStarCompUpperStarIso A f).hom).symm
  exact congrArg Iso.hom ((conjugateIsoEquiv
    ((Etale.upperStarLowerStarAdjunction A f).comp (comparisonAdjunction A X))
    ((comparisonAdjunction A Y).comp (ProEtale.upperStarLowerStarAdjunction A f))).apply_symm_apply
      (lowerStarCompComparisonLowerStarIso f A).symm).symm

end Underived

end ProEtale

end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section Derived

variable (Λ : Type (u + 1)) [CommRing Λ]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The counit of the derived adjunction `Lf^* ⊣ Rf_*` on pro-étale sheaves, on the image of a
complex `N`, precomposed with the unit of `Rf_*`, is the image of the levelwise counit. -/
lemma derivedUpperStarLowerStarAdjunction_counit_app_Qh_obj
    (N : HomotopyCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
      (ComplexShape.up ℤ)) :
    L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).map
        ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorUnit.app N) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app
        (DerivedCategory.Qh.obj N) =
    (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctorCounit.app
        (((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).mapHomotopyCategory _).obj N) ≫
      DerivedCategory.Qh.map
        (((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).mapHomotopyCategory
          (ComplexShape.up ℤ)).counit.app N) :=
  ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).mapHomotopyCategory
    (ComplexShape.up ℤ)).derivedε_fac_app _ _ _ N

/-- The counit of the bounded below derived adjunction `f^* ⊣ Rf_*` on étale sheaves, on the
image of a bounded below complex `K`, precomposed with `f^*` of the unit of `Rf_*`, is the
image of the levelwise counit. -/
lemma _root_.AlgebraicGeometry.Etale.derivedUpperStarLowerStarAdjunctionPlus_counit_app_fac
    (K : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f).map
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlusUnit.app K) ≫
      (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app
        (DerivedCategory.Plus.Qh.obj K) =
    (Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlusFactorsh.hom.app
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).mapHomotopyCategoryPlus.obj K) ≫
      DerivedCategory.Plus.Qh.map
        ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).mapHomotopyCategoryPlus.counit.app
          K) := by
  rw [Etale.derivedUpperStarLowerStarAdjunctionPlus, Adjunction.derivedAdjunctionPlus_eq_derivedPlus]
  exact Adjunction.derivedPlus_counit_app_fac _ K

/-- Blueprint `prop-weil-pbc-comparison-direct-image` (compatibility with the counits): the
comparison `ν_Y^* Rf_* ≅ Rf_* ν_X^*` is the mate of the comparison `ν_X^* f^* ≅ Lf^* ν_Y^*`, in
the transposed form: `ν_X^* f^* Rf_* M ≅ Lf^* ν_Y^* Rf_* M ⟶ Lf^* Rf_* ν_X^* M ⟶ ν_X^* M` is
`ν_X^*` of the counit of `f^* ⊣ Rf_*`. -/
theorem leftDerivedUpperStarComparisonIso_hom_app_comp_counit [QuasiCompact f]
    [QuasiSeparated f] (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (leftDerivedUpperStarComparisonIso f Λ).hom.app
        (R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj M) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).map
        ((rightDerivedLowerStarComparisonIso' f (ModuleCat.{u + 1} Λ)).hom.app M) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app
        (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj (DerivedCategory.Plus.ι.obj M)) =
    D(ν^*(X)[ModuleCat.{u + 1} Λ]).map (DerivedCategory.Plus.ι.map
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app M)) := by
  sorry

end Derived

end ProEtale

end AlgebraicGeometry
