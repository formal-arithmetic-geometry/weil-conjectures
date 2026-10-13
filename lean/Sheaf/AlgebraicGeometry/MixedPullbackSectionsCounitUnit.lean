/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.MixedAffineSectionsComplexUnit
public import Sheaf.AlgebraicGeometry.MixedGlobalSectionsDirectImageIso

/-! # Sections of the pullback counit and the normalized Leray unit
Source: Stacks Project, Tags 079W and 0D5T.
(blueprint: lem-sc-mixed-pullback-sections-counit-unit).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wA
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

/-- Apply sections to a pullback counit satisfying the underived unit factorization.
Source: Stacks Project, Tags 079W (derived adjunction) and 0D5T (Leray composition).
(blueprint: lem-sc-mixed-pullback-sections-counit-unit).

Proof: On the homotopy category write alpha for the ordinary pullback adjunction unit,
 beta for the right-derived direct-image unit, and s for the sections right-derived unit.
The hypothesis says eta followed by derived direct image of epsilon equals Q(alpha);beta.
Apply derived S-sections. Naturality of s at alpha moves Q(alpha) to ordinary sections.
Naturality of the normalized Leray isomorphism at epsilon moves sections of epsilon
across that isomorphism. Its defining unit equation then replaces s;sections(beta);Leray
by the ordinary direct-image/sections comparison followed by exact scalar restriction's
localization factor and restriction of the T-sections unit. The underived comparison is
identity on sections, so the ordinary map is precisely sections of alpha. Finally
conjugate by quotientCompQhIso and mapHomotopyCategoryFactors at C and g-star C.
Naturality of these factors identifies this conjugated ordinary map with Q(d_C), and
mapDerivedCategoryFactorsh with mapDerivedCategoryFactors. This proves the displayed
identity. No counit invertibility, affine hypothesis, K-flatness, boundedness or equality
between w and wA is needed; zero complexes and empty schemes obey the same naturalities. -/
theorem mixedPullback_sections_counit_unit {S T : Scheme.{u}} (g : T ⟶ S)
    [(Scheme.Modules.tensorPullback g).Additive]
    [(RingedSpace.globalSectionsFunctor S.toRingedSpace).Additive]
    [(RingedSpace.globalSectionsFunctor T.toRingedSpace).Additive]
    (C : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
    (ε : DerivedCategory.Qh ⋙ derivedPullback.{u, w} g ⟶
      (Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh
          (C := SheafOfModules.{u} (moduleRings T.toRingedSpace)))
    (hunit :
      (schemeHomPullbackAdjunction.{u, w} g).homEquiv
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj C))
          ((DerivedCategory.Qh
            (C := SheafOfModules.{u} (moduleRings T.toRingedSpace))).obj
            (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient _ (.up ℤ)).obj C)))
          (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj C) ≫
            (DerivedCategory.Qh
              (C := SheafOfModules.{u} (moduleRings T.toRingedSpace))).map (𝟙 _)) =
      (DerivedCategory.Qh
        (C := SheafOfModules.{u} (moduleRings S.toRingedSpace))).map
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).mapHomotopyCategory
          (.up ℤ)).homEquiv ((HomotopyCategory.quotient _ (.up ℤ)).obj C) _ (𝟙 _)) ≫
        (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctorUnit.app
          (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj C))) :
    let H := RingedSpace.globalSectionsFunctor S.toRingedSpace
    let J := RingedSpace.globalSectionsFunctor T.toRingedSpace
    let K : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings T.toRingedSpace) := Scheme.Modules.tensorPullback g
    let R := ModuleCat.restrictScalars.{u} g.appTop.hom
    let d : H ⟶ K ⋙ J ⋙ R := Functor.whiskerRight
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit H
    let D := (K.mapHomologicalComplex (.up ℤ)).obj C
    let e : (derivedPullback.{u, w} g).obj (DerivedCategory.Q.obj C) ⟶ DerivedCategory.Q.obj D :=
      (derivedPullback.{u, w} g).map ((DerivedCategory.quotientCompQhIso _).inv.app C) ≫
        ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj C) ≫
        (DerivedCategory.Qh
          (C := SheafOfModules.{u} (moduleRings T.toRingedSpace))).map
          ((K.mapHomotopyCategoryFactors (.up ℤ)).hom.app C) ≫
        (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (moduleRings T.toRingedSpace))).hom.app D
    mixedSectionsComplexUnit S C ≫
      (schemeDerivedGlobalSections S).map
        ((schemeHomPullbackAdjunction.{u, w} g).unit.app (DerivedCategory.Q.obj C)) ≫
      (mixedGlobalSectionsDirectImageIso g).hom.app
        ((derivedPullback.{u, w} g).obj (DerivedCategory.Q.obj C)) ≫
      (schemeGlobalScalarRestriction g).map ((schemeDerivedGlobalSections T).map e) =
    DerivedCategory.Q.map ((d.mapHomologicalComplex (.up ℤ)).app C) ≫
      R.mapDerivedCategoryFactors.inv.app ((J.mapHomologicalComplex (.up ℤ)).obj D) ≫
      (schemeGlobalScalarRestriction g).map (mixedSectionsComplexUnit T D) := by sorry

end AlgebraicGeometry
