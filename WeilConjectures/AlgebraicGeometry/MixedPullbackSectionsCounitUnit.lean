/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MixedAffineSectionsComplexUnit
public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

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

-- Both localization factor isomorphisms have identity components on complexes.
private theorem sectionsComplexUnit_eq (S : Scheme.{u})
    (C : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ) :
    mixedSectionsComplexUnit S C =
      (RingedSpace.globalSectionsFunctor S.toRingedSpace).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj C) := by
  simp only [mixedSectionsComplexUnit, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.id_comp, Category.comp_id]

set_option maxHeartbeats 800000 in
-- Comparing the scheme and sheaf presentations of module categories needs extra reduction.
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
      (schemeGlobalScalarRestriction g).map (mixedSectionsComplexUnit T D) := by
  let H := RingedSpace.globalSectionsFunctor S.toRingedSpace
  let J := RingedSpace.globalSectionsFunctor T.toRingedSpace
  let K : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings T.toRingedSpace) := Scheme.Modules.tensorPullback g
  let F := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
  let R := ModuleCat.restrictScalars.{u} g.appTop.hom
  let M := (HomotopyCategory.quotient _ (.up ℤ)).obj C
  let N := (K.mapHomotopyCategory (.up ℤ)).obj M
  let adj : K ⊣ F := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  let a : M ⟶ (F.mapHomotopyCategory (.up ℤ)).obj N :=
    (adj.mapHomotopyCategory (.up ℤ)).unit.app M
  let s := H.rightDerivedFunctorUnit
  let t := J.rightDerivedFunctorUnit
  let β := F.rightDerivedFunctorUnit
  let η := (schemeHomPullbackAdjunction.{u, w} g).unit
  let L := mixedGlobalSectionsDirectImageIso g
  let D := (K.mapHomologicalComplex (.up ℤ)).obj C
  let E := (J.mapHomologicalComplex (.up ℤ)).obj D
  let d : H ⟶ K ⋙ J ⋙ R := Functor.whiskerRight adj.unit H
  let e : (derivedPullback.{u, w} g).obj (DerivedCategory.Q.obj C) ⟶
      DerivedCategory.Q.obj D :=
    (derivedPullback.{u, w} g).map ((DerivedCategory.quotientCompQhIso _).inv.app C) ≫
      ε.app M ≫ DerivedCategory.Qh.map
        ((K.mapHomotopyCategoryFactors (.up ℤ)).hom.app C) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app D
  change mixedSectionsComplexUnit S C ≫
      (schemeDerivedGlobalSections S).map (η.app (DerivedCategory.Q.obj C)) ≫
      L.hom.app ((derivedPullback g).obj (DerivedCategory.Q.obj C)) ≫
      (schemeGlobalScalarRestriction g).map ((schemeDerivedGlobalSections T).map e) =
      DerivedCategory.Q.map ((d.mapHomologicalComplex (.up ℤ)).app C) ≫
      R.mapDerivedCategoryFactors.inv.app E ≫
      (schemeGlobalScalarRestriction g).map (mixedSectionsComplexUnit T D)
  have he : e = ε.app M := by
    change (derivedPullback.{u, w} g).map (𝟙 (DerivedCategory.Q.obj C)) ≫
      ε.app M ≫ DerivedCategory.Qh.map (𝟙 N) ≫ 𝟙 (DerivedCategory.Q.obj D) = _
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id, Category.comp_id]
  erw [sectionsComplexUnit_eq, sectionsComplexUnit_eq]
  rw [he]
  let c₀ := Classical.choose (exists_mixedGlobalSectionsDirectImageIso g)
  have hc := Classical.choose_spec
    (Classical.choose_spec (exists_mixedGlobalSectionsDirectImageIso g))
  have hc₀ : c₀ = Iso.refl (F ⋙ H) := by
    apply Iso.ext
    ext A x
    exact hc.1 A x
  have hL := hc.2 N
  change s.app ((F.mapHomotopyCategory (.up ℤ)).obj N) ≫
      (schemeDerivedGlobalSections S).map (β.app N) ≫ L.hom.app _ = _ at hL
  rw [show Classical.choose (exists_mixedGlobalSectionsDirectImageIso g) =
      Iso.refl (F ⋙ H) from hc₀] at hL
  change _ = DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ H)) (.up ℤ)).hom.app N ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ H)) (.up ℤ)).inv.app N) ≫
      R.mapDerivedCategoryFactorsh.inv.app ((J.mapHomotopyCategory (.up ℤ)).obj N) ≫
      (schemeGlobalScalarRestriction g).map (t.app N) at hL
  rw [Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp] at hL
  change (schemeHomPullbackAdjunction.{u, w} g).homEquiv
      (DerivedCategory.Qh.obj M) (DerivedCategory.Qh.obj N)
      (ε.app M ≫ DerivedCategory.Qh.map (𝟙 N)) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).homEquiv M N (𝟙 N)) ≫
      β.app N at hunit
  have hu : η.app (DerivedCategory.Qh.obj M) ≫
      (schemeDerivedDirectImage g).map (ε.app M) =
      DerivedCategory.Qh.map a ≫ β.app N := by
    erw [CategoryTheory.Functor.map_id, Category.comp_id,
      Adjunction.homEquiv_id, Adjunction.homEquiv_unit] at hunit
    exact hunit
  have hh : s.app M ≫ (schemeDerivedGlobalSections S).map
      (η.app (DerivedCategory.Qh.obj M)) ≫
      L.hom.app ((derivedPullback g).obj (DerivedCategory.Qh.obj M)) ≫
      (schemeGlobalScalarRestriction g).map
        ((schemeDerivedGlobalSections T).map (ε.app M)) =
      DerivedCategory.Qh.map ((H.mapHomotopyCategory (.up ℤ)).map a) ≫
      R.mapDerivedCategoryFactorsh.inv.app ((J.mapHomotopyCategory (.up ℤ)).obj N) ≫
      (schemeGlobalScalarRestriction g).map (t.app N) := by
    erw [← L.hom.naturality (ε.app M)]
    change s.app M ≫ (schemeDerivedGlobalSections S).map
      (η.app (DerivedCategory.Qh.obj M)) ≫
      (schemeDerivedGlobalSections S).map ((schemeDerivedDirectImage g).map (ε.app M)) ≫
      L.hom.app _ = _
    rw [← Functor.map_comp_assoc, hu, Functor.map_comp]
    simp only [Category.assoc]
    erw [← s.naturality_assoc a]
    simp only [Functor.comp_map]
    erw [hL]
  have ha : (H.mapHomotopyCategory (.up ℤ)).map a =
      (HomotopyCategory.quotient _ (.up ℤ)).map
        ((d.mapHomologicalComplex (.up ℤ)).app C) := by
    dsimp only [a, M]
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
    rw [Functor.mapHomotopyCategory_map]
    congr 1
  have hfac := R.mapDerivedCategoryFactorsh_hom_app E
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv] at hfac
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, Category.comp_id] at hfac
  have hR : R.mapDerivedCategoryFactorsh.inv.app
      ((J.mapHomotopyCategory (.up ℤ)).obj N) =
      R.mapDerivedCategoryFactors.inv.app E := by
    apply (cancel_mono (R.mapDerivedCategoryFactors.hom.app E)).1
    erw [← hfac]
    erw [Iso.inv_hom_id_app]
    erw [hfac, Iso.inv_hom_id_app]
    rfl
  erw [ha, hR] at hh
  exact hh

end AlgebraicGeometry
