/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs

/-! # Section complexes used in the flat base-change calculation

Source: Stacks Project, Cohomology of Sheaves, Tags 01E4 and 01FB
(blueprint: def-weil-pbc-flat-base-change-section-complex).
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives

/-- Evaluate a direct-image map of complexes on an open.
Source: Stacks, Tags 01FB and 02N7
(blueprint: def-weil-pbc-flat-base-change-section-complex). -/
def pushforwardComplexSections {X Y : Scheme.{u}} (g : X ⟶ Y)
    {K : CochainComplex Y.Modules ℕ} {L : CochainComplex X.Modules ℕ}
    (q : K ⟶ ((pushforward g).mapHomologicalComplex (ComplexShape.up ℕ)).obj L)
    (V : Y.Opens) :
    ((RingedSpace.openModuleSections Y.toRingedSpace V).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K ⟶
    ((RingedSpace.openModuleSections X.toRingedSpace (g ⁻¹ᵁ V)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj L where
  f n := Hom.app (q.f n) V
  comm' i j _ := congrArg (fun a ↦ Hom.app a V) (q.comm i j)

/-- The class of a section cocycle in the cohomology sheaf.
Source: Stacks, Tag 01E4
(blueprint: def-weil-pbc-flat-base-change-section-complex). -/
def sectionHomologyClass {Y : Scheme.{u}} (K : CochainComplex Y.Modules ℕ)
    (V : Y.Opens) (p : ℕ) :
    (((RingedSpace.openModuleSections Y.toRingedSpace V).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).homology p ⟶ (K.homology p).presheaf.obj (op V) :=
  (((((SheafOfModules.forget Y.ringCatSheaf).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K).sc p).mapHomologyIso
      (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙
        (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V))).hom ≫
    ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
      (sectionCohomologyTheta K p)).app (op V)

/-- Transport derived global cohomology to homology of a specified section complex.
Source: Stacks, Tags 01E4 and 01FB
(blueprint: def-weil-pbc-flat-base-change-section-complex). -/
def resolutionSectionHomology {Z Y : Scheme.{u}} {G : Z.Modules}
    (R : InjectiveResolution G) (K : CochainComplex Y.Modules ℕ) (V : Y.Opens)
    (a : ((RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        R.cocomplex ≅
      ((RingedSpace.openModuleSections Y.toRingedSpace V).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K) (p : ℕ) :
    (forget₂ _ AddCommGrpCat.{u}).obj
      ((RingedSpace.moduleCohomology Z.toRingedSpace p).obj G) ⟶
    (((RingedSpace.openModuleSections Y.toRingedSpace V).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).homology p :=
  letI := RingedSpace.globalSectionsFunctor_additive Z.toRingedSpace
  (forget₂ _ AddCommGrpCat.{u}).map
    (R.isoRightDerivedObj (RingedSpace.globalSectionsFunctor Z.toRingedSpace) p).hom ≫
    (((RingedSpace.globalSectionsComplex R).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{u})).inv ≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map a.hom

/-- The section class map factors through section-complex homology.
Source: Stacks, Tag 01E4
(blueprint: def-weil-pbc-flat-base-change-section-complex). -/
theorem resolutionSectionClass_factor {Z Y : Scheme.{u}} {G : Z.Modules}
    (R : InjectiveResolution G) (K : CochainComplex Y.Modules ℕ) (V : Y.Opens)
    (a : ((RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        R.cocomplex ≅
      ((RingedSpace.openModuleSections Y.toRingedSpace V).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K) (p : ℕ) :
    resolutionSectionClass R K V a p =
      resolutionSectionHomology R K V a p ≫ sectionHomologyClass K V p := by
  dsimp only [resolutionSectionClass, resolutionSectionHomology, sectionHomologyClass]
  simp only [Category.assoc]


end AlgebraicGeometry.Scheme.Modules
