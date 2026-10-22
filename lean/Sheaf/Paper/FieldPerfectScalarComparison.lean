/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.FieldDerivedScalarTower
public import Sheaf.CategoryTheory.DerivedCategory.PerfectScalarTensorCoherence
public import Sheaf.CategoryTheory.LocalizationLeftDerivedComparison

/-! # Derived scalar extension over fields is the exact scalar extension

Source: blueprint order 1826, conditional construction step 6
(blueprint: lem-sf-field-perfect-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor
namespace DerivedCategory.PerfectScalar
variable {K L : Type u} [Field K] [Field L]

/-- Removing the regular degree-zero factor is the ordinary scalar extension.
Source: Stacks 06Y6 (blueprint: lem-sf-field-perfect-scalar-comparison). -/
def ordinaryScalarComparison (f : K →+* L) :
    (ModuleCat.mixedTensor f).flip.map₂CochainComplex.flip.obj (coefficient (.of L)) ≅
      E (CommRingCat.ofHom f) :=
  CochainComplex.map₂HomologicalComplexFlipObjSingleIso (ModuleCat.mixedTensor f).flip
      (ModuleCat.of L L) ≪≫
    NatIso.mapHomologicalComplex
      (isoWhiskerLeft (ModuleCat.extendScalars f) (leftUnitorNatIso (ModuleCat L)) ≪≫
        Functor.rightUnitor _) (.up ℤ)

/-- The canonical derived counit before removing the regular coefficient factor.
Source: Stacks 06Y6 (blueprint: lem-sf-field-perfect-scalar-comparison). -/
def scalarCounit (f : K →+* L) :
    Q ⋙ B (CommRingCat.ofHom f) ⟶
      (ModuleCat.mixedTensor f).flip.map₂CochainComplex.flip.obj (coefficient (.of L)) ⋙ Q := by
  unfold B
  exact Classical.choose (Classical.choose_spec (exists_derivedTensor_second_factor_functor f).2)
    (coefficient (.of L))

/-- Its universal property is exactly the recorded left-derived property.
Source: Stacks 06Y6 (blueprint: lem-sf-field-perfect-scalar-comparison). -/
theorem scalarCounit_derived (f : K →+* L) :
    (B (CommRingCat.ofHom f)).IsLeftDerivedFunctor (scalarCounit f)
      (HomologicalComplex.quasiIso (ModuleCat K) (.up ℤ)) := by
  unfold B scalarCounit
  exact (Classical.choose_spec (Classical.choose_spec
    (exists_derivedTensor_second_factor_functor f).2)).1 (coefficient (.of L))

/-- The actual scalar functor agrees canonically with exact termwise extension.
Source: blueprint order 1826, step 6
(blueprint: lem-sf-field-perfect-scalar-comparison). -/
def fieldScalarComparison (f : K →+* L) :
    B (CommRingCat.ofHom f) ≅ fieldDerivedScalarExtension f := by
  letI := scalarCounit_derived f
  exact Functor.localizationLeftDerivedComparison Q
    (HomologicalComplex.quasiIso (ModuleCat K) (.up ℤ)) _ _ _ (scalarCounit f)
    ((ModuleCat.extendScalars f).mapDerivedCategoryFactors ≪≫
      isoWhiskerRight (ordinaryScalarComparison f).symm Q)

/-- On every complex, this is precisely the prescribed computation map.
Source: blueprint order 1826, step 6
(blueprint: lem-sf-field-perfect-scalar-comparison). -/
theorem fieldScalarComparison_model (f : K →+* L)
    (P : CochainComplex (ModuleCat K) ℤ) :
    (fieldScalarComparison f).hom.app (Q.obj P) ≫
        (ModuleCat.extendScalars f).mapDerivedCategoryFactors.hom.app P =
      modelMap (CommRingCat.ofHom f) P := by
  letI := scalarCounit_derived f
  have hf := congr_app (Functor.localizationLeftDerivedComparison_fac Q
    (HomologicalComplex.quasiIso (ModuleCat K) (.up ℤ)) _ _ _ (scalarCounit f)
    ((ModuleCat.extendScalars f).mapDerivedCategoryFactors ≪≫
      isoWhiskerRight (ordinaryScalarComparison f).symm Q)) P
  dsimp only [NatTrans.comp_app, whiskerLeft_app, Iso.trans_hom, Iso.app_hom,
    isoWhiskerRight_hom, whiskerRight_app, Iso.symm_hom] at hf
  apply (cancel_mono (Q.map ((ordinaryScalarComparison f).inv.app P))).1
  rw [Category.assoc]
  change (fieldScalarComparison f).hom.app (Q.obj P) ≫ _ = _ at hf
  rw [hf]
  unfold modelMap
  change (scalarCounit f).app P = ((scalarCounit f).app P ≫
    Q.map ((ordinaryScalarComparison f).hom.app P)) ≫
      Q.map ((ordinaryScalarComparison f).inv.app P)
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    Category.comp_id]
  rw [Q.map_id]
  exact (Category.comp_id ((scalarCounit f).app P)).symm

end DerivedCategory.PerfectScalar
