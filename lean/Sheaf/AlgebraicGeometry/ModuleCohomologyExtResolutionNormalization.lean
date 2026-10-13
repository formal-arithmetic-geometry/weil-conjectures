/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
import Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives
import Sheaf.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural

/-! # Computing the fixed comparison on arbitrary injective resolutions

Source: Stacks Project, Tags 03FD and 015E.
(blueprint: new-module-cohomology-ext-resolution-normalization)
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution

attribute [local instance] enoughInjectives

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev moduleSections (X : Scheme.{u}) :=
  RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙ forget₂ _ AddCommGrpCat.{u}

abbrev abelianSections (X : Scheme.{u}) :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)

/-- The concrete comparison from module cohomology to the sections of a resolution.
Source: Stacks Project, Tag 01DZ, injective-resolution computation. -/
def moduleResolutionIso (X : Scheme.{u}) {F : SheafOfModules.{u} (moduleRings X.toRingedSpace)}
    (I : InjectiveResolution F) (p : ℕ) :
    (forget₂ _ AddCommGrpCat.{u}).obj
      ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F) ≅
    (((moduleSections X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex).homology p := by
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  exact (forget₂ _ AddCommGrpCat.{u}).mapIso
    (I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) p) ≪≫
    (((RingedSpace.globalSectionsComplex I).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{u})).symm

set_option backward.isDefEq.respectTransparency false in
/-- The Ext comparison to sections of a specified module resolution, using the
forgotten augmentation and its canonical acyclic-resolution comparison.
Source: Stacks Project, Tags 03FD, 015E and 06XR. -/
def abelianResolutionIso (X : Scheme.{u}) {F : SheafOfModules.{u} (moduleRings X.toRingedSpace)}
    (I : InjectiveResolution F) (p : ℕ) :
    AddCommGrpCat.of (H F p) ≅
    (((moduleSections X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex).homology p := by
  let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
  let ι := (HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℕ) 0).inv.app F ≫
    (T.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
  have : QuasiIso ι := by
    dsimp only [ι]
    have : QuasiIso ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι) :=
      inferInstance
    exact quasiIso_comp _ _
  exact (Abelian.Ext.precompAddEquiv (terminalSourceIso X) (T.obj F) p).toAddCommGrpIso ≪≫
    siteSectionsObjIso (Opens.grothendieckTopology X) ⊤ (T.obj F) p ≪≫
    (abelianSections X).rightDerivedObjIsoOfResolution ι
      (fun n ↦ forgottenInjectiveAcyclic X (I.cocomplex.X n)) p

set_option backward.isDefEq.respectTransparency false in
/-- The fixed comparison can be computed on any injective module resolution.
Source: Stacks Project, Tag 015E, naturality of acyclic-resolution comparisons;
Tag 03FD, acyclicity of forgotten injective modules.
(blueprint: new-module-cohomology-ext-resolution-normalization)

Proof: Lift the identity from the standard module resolution to I. Naturality
of isoRightDerivedObj and of exact forgetting of homology makes the module
comparison commute with the section homology of this lift. Apply
acyclicComparison_naturality to the forgotten lift and augmentations: their
terms are section-acyclic by forgottenInjectiveAcyclic. Hence the abelian
comparison commutes with exactly the same section homology map. This map is
invertible, since a lift of the identity between injective resolutions is a
homotopy equivalence. Cancel it. The remaining Ext/source comparisons are
identical on both sides. For the standard resolution the equality is the
definition of moduleCohomologyExtResolutionEquiv. The argument includes p=0,
empty schemes and zero modules, and involves no scheme morphism or edge map. -/
theorem moduleCohomologyExtResolutionEquiv_normalization
    (X : Scheme.{u}) {F : SheafOfModules.{u} (moduleRings X.toRingedSpace)}
    (I : InjectiveResolution F) (p : ℕ)
    (x : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F) :
    (abelianResolutionIso X I p).hom (moduleCohomologyExtResolutionEquiv X F p x) =
      (moduleResolutionIso X I p).hom x := by
  sorry

end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
