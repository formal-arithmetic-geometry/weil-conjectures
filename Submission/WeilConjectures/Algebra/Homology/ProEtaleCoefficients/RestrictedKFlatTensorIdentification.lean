/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Restricted scalar-first K-flat tensor identifications

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 06YT, and
sites-modules.tex, Tags 03EK and 03CY.
(blueprint: lem-pe-restricted-kflat-tensor-identification)

The scalar-last complex is specified by its underlying B-linear tensor complex and
its S-linear swap from the existing scalar-first extension. The pure-tensor equation
fixes the swap, including its inverse, and hence fixes the S-action on the last factor.
No existence choice of an unspecified object or map is used in a definition.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
universe u v r wB wA wS wT
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

/-- Ordinary scalar restriction on the given site.
Source: Stacks 03DA (blueprint: lem-pe-restricted-kflat-tensor-identification). -/
noncomputable abbrev restrictedTensorScalars {A S : Sheaf J CommRingCat.{r}} (v : A ⟶ S) :=
  restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map v)

/-- The coefficient sheaf as a module over the source ring.
Source: Stacks 03EK (blueprint: lem-pe-restricted-kflat-tensor-identification). -/
noncomputable abbrev restrictedTensorCoefficient
    {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S) :=
  (restrictedTensorScalars φ).obj (unit (derivedChangeRingIndependentCoefficients J S))

namespace RestrictedTensorProof

variable [HasWeakSheafify J AddCommGrpCat.{r}]

attribute [local irreducible] monoidalCategory cochainModulesMonoidal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option hygiene false in
local notation "𝓡" R => derivedChangeRingIndependentCoefficients J R
set_option hygiene false in
local notation "𝓻" a => (sheafCompose J (forget₂ CommRingCat RingCat)).map a

private noncomputable def restrictSheafifyHom
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S) (M : PresheafOfModules.{r} S.obj) :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj
      ((PresheafOfModules.restrictScalars α.hom).obj M) ⟶
    (restrictScalars α).obj ((PresheafOfModules.sheafification (𝟙 S.obj)).obj M) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
    ((PresheafOfModules.restrictScalars α.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).unit.app M))

private theorem restrictSheafifyHom_toSheaf
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S) (M : PresheafOfModules.{r} S.obj) :
    (toSheaf R).map (restrictSheafifyHom α M) =
      𝟙 ((PresheafOfModules.toPresheaf S.obj ⋙
        presheafToSheaf J AddCommGrpCat).obj M) := by
  rw [restrictSheafifyHom, PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  apply ((CategoryTheory.sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  change (PresheafOfModules.toPresheaf S.obj).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).unit.app M) =
    CategoryTheory.toSheafify J M.presheaf
  exact PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app _ _

attribute [local irreducible] restrictSheafifyHom

private theorem restrictSheafifyHom_isIso
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S) (M : PresheafOfModules.{r} S.obj) :
    IsIso (restrictSheafifyHom α M) := by
  have : IsIso ((toSheaf R).map (restrictSheafifyHom α M)) := by
    rw [restrictSheafifyHom_toSheaf]
    exact IsIso.id _
  exact isIso_of_reflects_iso _ (toSheaf R)

attribute [local instance] restrictSheafifyHom_isIso

private noncomputable def restrictSheafifyIso
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S) (M : PresheafOfModules.{r} S.obj) :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj
      ((PresheafOfModules.restrictScalars α.hom).obj M) ≅
    (restrictScalars α).obj ((PresheafOfModules.sheafification (𝟙 S.obj)).obj M) :=
  asIso (restrictSheafifyHom α M)

attribute [local irreducible] restrictSheafifyIso

private noncomputable def swapApp {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    (M : SheafOfModules.{r} (𝓡 B)) (U : Cᵒᵖ) :
    ((PresheafOfModules.restrictScalars (𝓻 φ).hom).obj
      (changeOfRingsPresheaf φ M)).obj U ≅
    (siteTensorPresheaf M.val (restrictedTensorCoefficient φ).val).obj U := by
  let e : (((PresheafOfModules.restrictScalars (𝓻 φ).hom).obj
      (changeOfRingsPresheaf φ M)).obj U) ≃ₗ[B.obj.obj U]
      TensorProduct (B.obj.obj U) ((restrictedTensorCoefficient φ).val.obj U) (M.val.obj U) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro b x
        induction x using TensorProduct.inductionOn with
        | tmul s m => rfl
        | add x y hx hy => simpa only [smul_add] using congrArg₂ (· + ·) hx hy }
  exact (e.trans (TensorProduct.comm _ _ _)).toModuleIso

private theorem swapApp_tmul {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    (M : SheafOfModules.{r} (𝓡 B)) (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    (swapApp φ M U).hom (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] m) =
      m ⊗ₜ[B.obj.obj U] (show (restrictedTensorCoefficient φ).val.obj U from s) := rfl

attribute [local irreducible] swapApp

private noncomputable def swapPresheafIso {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    (M : SheafOfModules.{r} (𝓡 B)) :
    (PresheafOfModules.restrictScalars (𝓻 φ).hom).obj (changeOfRingsPresheaf φ M) ≅
      siteTensorPresheaf M.val (restrictedTensorCoefficient φ).val :=
  PresheafOfModules.isoMk (swapApp φ M) (by
    intro U V i
    ext x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s m =>
      change (swapApp φ M V).hom (changeOfRingsMap φ M i
        (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] m)) = _
      erw [Classical.choose_spec (exists_changeOfRingsMap φ M i) s m]
      rw [swapApp_tmul]
      change _ = (siteTensorPresheaf M.val (restrictedTensorCoefficient φ).val).map i
        ((swapApp φ M U).hom (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] m))
      rw [swapApp_tmul]
      rfl)

attribute [local irreducible] swapPresheafIso

private noncomputable def swapSheafIso {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    (M : SheafOfModules.{r} (𝓡 B)) :
    (restrictedTensorScalars φ).obj (changeOfRings φ M) ≅
      (siteSheafTensorRight (restrictedTensorCoefficient φ)).obj M :=
  (restrictSheafifyIso (𝓻 φ) (changeOfRingsPresheaf φ M)).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 (𝓡 B).obj)).mapIso (swapPresheafIso φ M)

attribute [local irreducible] swapSheafIso



end RestrictedTensorProof

variable {B A S T : Sheaf J CommRingCat.{r}}
  [HasDerivedCategory.{wB} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J B))]
  [HasDerivedCategory.{wA} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J A))]
  [HasDerivedCategory.{wS} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J S))]

open RestrictedTensorProof

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable [HasDerivedCategory.{wT} (ringedSiteModules.{r}
  (derivedChangeRingIndependentCoefficients J T))]

end SheafOfModules
