/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.Algebra.Homology.RingIsomorphismTensorTransport
public import Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition

/-! # Canonical comparisons for coefficient restriction

Source: Stacks Project, Tags 03D7, 015F and 04VG.

(blueprint: lem-pur-u2-restriction-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r w
open CategoryTheory CategoryTheory.Limits
attribute [local irreducible] SheafOfModules.monoidalCategory

namespace SheafOfModules.RingIsoTransport

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (scalarModules J R)]

/-- Identity restriction is identity on sections.
Source: literature/stacks-project/derived.tex; literature/stacks-project/categories.tex; Tag 015F
and Tags 04VG/04VK; exact restriction unit/composition localization formulas.
(blueprint: lem-pur-u2-restriction-comparisons). -/
def ordinaryId (R : Sheaf J CommRingCat.{r}) :
    scalarRestriction (Iso.refl R).inv ≅ 𝟭 (scalarModules J R) :=
  NatIso.ofComponents (fun M ↦ Iso.refl _) (by intros; rfl)

/-- Successive restrictions compose by identity on sections.
Source: literature/stacks-project/derived.tex; literature/stacks-project/categories.tex; Tag 015F
and Tags 04VG/04VK; exact restriction unit/composition localization formulas.
(blueprint: lem-pur-u2-restriction-comparisons). -/
def ordinaryComp {R S T : Sheaf J CommRingCat.{r}} (a : R ≅ S) (b : S ≅ T) :
    scalarRestriction a.inv ⋙ scalarRestriction b.inv ≅ scalarRestriction (a ≪≫ b).inv :=
  NatIso.ofComponents (fun M ↦ Iso.refl _) (by intros; rfl)

/-- Identity restriction on complexes.
Source: literature/stacks-project/derived.tex; literature/stacks-project/categories.tex; Tag 015F
and Tags 04VG/04VK; exact restriction unit/composition localization formulas.
(blueprint: lem-pur-u2-restriction-comparisons). -/
def chainId (R : Sheaf J CommRingCat.{r}) :
    (scalarRestriction (Iso.refl R).inv).mapHomologicalComplex (.up ℤ) ≅
      𝟭 (CochainComplex (scalarModules J R) ℤ) :=
  NatIso.ofComponents (fun M ↦ Iso.refl _) (by intros; rfl)

/-- Successive restrictions on complexes.
Source: literature/stacks-project/derived.tex; literature/stacks-project/categories.tex; Tag 015F
and Tags 04VG/04VK; exact restriction unit/composition localization formulas.
(blueprint: lem-pur-u2-restriction-comparisons). -/
def chainComp {R S T : Sheaf J CommRingCat.{r}} (a : R ≅ S) (b : S ≅ T) :
    (scalarRestriction a.inv).mapHomologicalComplex (.up ℤ) ⋙
      (scalarRestriction b.inv).mapHomologicalComplex (.up ℤ) ≅
        (scalarRestriction (a ≪≫ b).inv).mapHomologicalComplex (.up ℤ) :=
  NatIso.ofComponents (fun M ↦ Iso.refl _) (by intros; rfl)

private instance restrictionAdditive {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    (scalarRestriction a).Additive := inferInstance


attribute [local irreducible] ordinaryId ordinaryComp


/-- The localization of the identity comparison.
Source: literature/stacks-project/derived.tex; literature/stacks-project/categories.tex; Tag 015F
and Tags 04VG/04VK; exact restriction unit/composition localization formulas.
(blueprint: lem-pur-u2-restriction-comparisons). -/
def derivedId (R : Sheaf J CommRingCat.{r}) :=
  Functor.exactDerivedRestrictionUnit _ (ordinaryId R)

/-- The localization of the composition comparison.
Source: literature/stacks-project/derived.tex; literature/stacks-project/categories.tex; Tag 015F
and Tags 04VG/04VK; exact restriction unit/composition localization formulas.
(blueprint: lem-pur-u2-restriction-comparisons). -/
def derivedComp {R S T : Sheaf J CommRingCat.{r}} (a : R ≅ S) (b : S ≅ T) :=
  Functor.exactDerivedRestrictionComposition _ _ _ (ordinaryComp a b)

omit [EssentiallySmall.{r} C] [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (scalarModules J R)] in
/-- The identity chain comparison fixes each section.
Source: literature/stacks-project/derived.tex; literature/stacks-project/categories.tex; Tag 015F
and Tags 04VG/04VK; exact restriction unit/composition localization formulas.
(blueprint: lem-pur-u2-restriction-comparisons). -/
theorem chainId_sections (R : Sheaf J CommRingCat.{r})
    (P : CochainComplex (scalarModules J R) ℤ) (n : ℤ) (U : Cᵒᵖ)
    (x : (P.X n).val.obj U) :
    (((chainId R).hom.app P).f n).val.app U x = x := rfl

omit [EssentiallySmall.{r} C] [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (scalarModules J R)] in
/-- The composition chain comparison fixes each section.
Source: literature/stacks-project/derived.tex; literature/stacks-project/categories.tex; Tag 015F
and Tags 04VG/04VK; exact restriction unit/composition localization formulas.
(blueprint: lem-pur-u2-restriction-comparisons). -/
theorem chainComp_sections {R S T : Sheaf J CommRingCat.{r}}
    (a : R ≅ S) (b : S ≅ T) (P : CochainComplex (scalarModules J R) ℤ)
    (n : ℤ) (U : Cᵒᵖ) (x : (P.X n).val.obj U) :
    (((chainComp a b).hom.app P).f n).val.app U x = x := rfl

omit [EssentiallySmall.{r} C] [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (scalarModules J R)] in
private theorem chainId_canonical (R : Sheaf J CommRingCat.{r})
    (P : CochainComplex (scalarModules J R) ℤ) :
    (((NatIso.mapHomologicalComplex (ordinaryId R) (.up ℤ)) ≪≫
      Functor.mapHomologicalComplexIdIso (scalarModules J R) (.up ℤ)).hom.app P) =
        (chainId R).hom.app P := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [ordinaryId, chainId, NatIso.ofComponents_hom_app, Iso.refl_hom,
    NatIso.mapHomologicalComplex_hom_app_f, Iso.trans_hom, NatTrans.comp_app,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplexIdIso_hom_app_f,
    HomologicalComplex.id_f]
  erw [Category.id_comp]
  rfl

omit [EssentiallySmall.{r} C] [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (scalarModules J R)] in
private theorem chainComp_canonical {R S T : Sheaf J CommRingCat.{r}}
    (a : R ≅ S) (b : S ≅ T) (P : CochainComplex (scalarModules J R) ℤ) :
    (NatIso.mapHomologicalComplex (ordinaryComp a b) (.up ℤ)).hom.app P =
      (chainComp a b).hom.app P := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [ordinaryComp, chainComp, NatIso.ofComponents_hom_app, Iso.refl_hom,
    NatIso.mapHomologicalComplex_hom_app_f, HomologicalComplex.id_f]
  rfl

attribute [local irreducible] chainId chainComp derivedId derivedComp

/-- The identity comparison has its specified localization formula.
Source: literature/stacks-project/derived.tex; literature/stacks-project/categories.tex; Tag 015F
and Tags 04VG/04VK; exact restriction unit/composition localization formulas.
(blueprint: lem-pur-u2-restriction-comparisons). -/
theorem derivedId_fac (R : Sheaf J CommRingCat.{r})
    (P : CochainComplex (scalarModules J R) ℤ) :
    (derivedId R).hom.app (DerivedCategory.Q.obj P) =
      (scalarRestriction (Iso.refl R).inv).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((chainId R).hom.app P) := by
  apply (cancel_epi
    ((scalarRestriction (Iso.refl R).inv).mapDerivedCategoryFactors.inv.app P)).1
  rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rw [← chainId_canonical]
  unfold derivedId
  exact
    Functor.exactDerivedRestrictionUnit_inv_factors _ (ordinaryId R) P

/-- The composition comparison has its specified localization formula.
Source: literature/stacks-project/derived.tex; literature/stacks-project/categories.tex; Tag 015F
and Tags 04VG/04VK; exact restriction unit/composition localization formulas.
(blueprint: lem-pur-u2-restriction-comparisons). -/
theorem derivedComp_fac {R S T : Sheaf J CommRingCat.{r}} (a : R ≅ S) (b : S ≅ T)
    (P : CochainComplex (scalarModules J R) ℤ) :
    (derivedComp a b).hom.app (DerivedCategory.Q.obj P) ≫
        (scalarRestriction (a ≪≫ b).inv).mapDerivedCategoryFactors.hom.app P =
      (scalarRestriction b.inv).mapDerivedCategory.map
          ((scalarRestriction a.inv).mapDerivedCategoryFactors.hom.app P) ≫
        (scalarRestriction b.inv).mapDerivedCategoryFactors.hom.app
          (((scalarRestriction a.inv).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((chainComp a b).hom.app P) := by
  rw [← chainComp_canonical]
  unfold derivedComp
  exact
    Functor.exactDerivedRestrictionComposition_hom_factors _ _ _ (ordinaryComp a b) P


end SheafOfModules.RingIsoTransport
