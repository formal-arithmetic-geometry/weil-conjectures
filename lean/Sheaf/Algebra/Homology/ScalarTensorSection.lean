/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
/-! # The sheafified pure scalar tensor of a cochain model -/
@[expose] public section
set_option autoImplicit false
universe u v r wR wS wV
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace CategoryTheory.PrincipalQuotientCompletion
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  {R S V : Sheaf J CommRingCat.{r}} {a : R ⟶ S} {b : S ⟶ V}
  [HasDerivedCategory.{wR}
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
  [HasDerivedCategory.{wS}
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
  [HasDerivedCategory.{wV}
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J V))]


/-- A sheafified pure tensor, transported through the model's prescribed object equality.
Source: Stacks 03EK, balanced formula in DAG proof step 1
(blueprint: def-trf-scalar-tensor-section). -/
noncomputable def scalarTensorSection
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel a)
    (M : ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) : (F.E.obj M).val.obj U :=
  (eqToHom (F.obj_eq M).symm).val.app U
    ((toSheafify J (SheafOfModules.changeOfRingsPresheaf a M).presheaf).app U
      (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x))


end CategoryTheory.PrincipalQuotientCompletion
