/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.LinearAlgebra.FreeModule.PID
import Sheaf.Algebra.Homology.FiniteFreeResolutionTensor
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.FromJoel.Algebra.Homology.Double
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # Finite free resolutions of scalar models

Source: Weil conjectures blueprint, main-20261015, sec-proetale-coefficients,
ctf-equals-bc proof, Local models; Stacks Tags 03EI, 06YQ, 06YS, 06YP and 06YU
(blueprint: lem-sfb-scalar-model-finite-flat-resolution).

## Main definitions

- `CategoryTheory.siteConstantModuleFunctorIndependent`: constant modules at independent
  coefficient universe, preserving the existing dependency interface by import.
- `CategoryTheory.commutativeConstantModuleIndependent`: its commutative-ring presentation.

## Main statements

- `scalarModel_finite_flat_resolution_dvr`: the DVR resolution and tensor computation.
- `scalarModel_finite_free_field`: the field case without flatness of the algebra sheaf.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r w uA vA
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The constant module presheaf with identity restrictions, in independent universes.
Source: Stacks 03CY and 093T (blueprint: lem-sfb-scalar-model-finite-flat-resolution). -/
def siteConstantModulePresheafIndependent (R : Type r) [CommRing R] :
    ModuleCat.{r} R ⥤ PresheafOfModules.{r} ((Functor.const Cᵒᵖ).obj (RingCat.of R)) where
  obj M := { obj := fun _ ↦ M, map := fun _ ↦ ModuleCat.ofHom LinearMap.id }
  map f := { app := fun _ ↦ f }

variable (J : GrothendieckTopology C) [EssentiallySmall.{r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J RingCat.{r}] [HasSheafify J CommRingCat.{r}]
  [J.WEqualsLocallyBijective RingCat.{r}]
  [J.WEqualsLocallyBijective CommRingCat.{r}]

/-- Constant module sheafification over the constant ring sheaf.
Source: Stacks 03CY and 093T (blueprint: lem-sfb-scalar-model-finite-flat-resolution). -/
def siteConstantModuleFunctorIndependent (R : Type r) [CommRing R] :
    ModuleCat.{r} R ⥤ SheafOfModules.{r}
      ((constantSheaf J RingCat.{r}).obj (RingCat.of R)) :=
  siteConstantModulePresheafIndependent (C := C) R ⋙
    PresheafOfModules.sheafification
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))

/-- The same coefficient ring, formed in commutative rings before forgetting.
Source: Stacks 093T (blueprint: lem-sfb-scalar-model-finite-flat-resolution). -/
abbrev independentConstantRing (R : Type r) [CommRing R] : Sheaf J CommRingCat.{r} :=
  (constantSheaf J CommRingCat.{r}).obj (CommRingCat.of R)

/-- The commutative-ring sheafification unit with commutativity forgotten.
Source: Stacks 03CY (blueprint: lem-sfb-scalar-model-finite-flat-resolution). -/
def independentConstantRingUnit (R : Type r) [CommRing R] :
    (Functor.const Cᵒᵖ).obj (RingCat.of R) ⟶
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
        (independentConstantRing J R)).obj :=
  Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of R)))
    (forget₂ CommRingCat.{r} RingCat.{r})

-- Keep the existing instance parameters in the public interface.
set_option linter.unusedSectionVars false in
/-- Forgetting commutativity preserves local bijectivity of the coefficient unit.
Source: Stacks 03CY (blueprint: lem-sfb-scalar-model-finite-flat-resolution).
Proof: the functions on sections and their equalizer and image covering sieves do not
change under forgetting commutativity. The ring-sheafification unit is locally bijective. -/
theorem independentConstantRingUnit_locallyBijective (R : Type r) [CommRing R] :
    Presheaf.IsLocallyInjective J (independentConstantRingUnit J R) ∧
      Presheaf.IsLocallySurjective J (independentConstantRingUnit J R) := by
  constructor
  · apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
    change Presheaf.IsLocallyInjective J (Functor.whiskerRight (toSheafify J
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))) (forget CommRingCat.{r}))
    infer_instance
  · apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
    change Presheaf.IsLocallySurjective J (Functor.whiskerRight (toSheafify J
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))) (forget CommRingCat.{r}))
    infer_instance

/-- Sheafify the same constant module presheaf over the commutative coefficient presentation.
Source: Stacks 03CY and 093T (blueprint: lem-sfb-scalar-model-finite-flat-resolution). -/
def commutativeConstantModuleIndependent (R : Type r) [CommRing R] :
    ModuleCat.{r} R ⥤ SheafOfModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj (independentConstantRing J R)) :=
  letI := (independentConstantRingUnit_locallyBijective J R).1
  letI := (independentConstantRingUnit_locallyBijective J R).2
  siteConstantModulePresheafIndependent (C := C) R ⋙
    PresheafOfModules.sheafification (independentConstantRingUnit J R)

end CategoryTheory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]

/-- Module sheaves over the given commutative ring sheaf, using the existing category.
Source: Stacks 03DA (blueprint: lem-sfb-scalar-model-finite-flat-resolution). -/
abbrev scalarModelModules (B : Sheaf J CommRingCat.{r}) :=
  SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj B)

variable [EssentiallySmall.{r} C]

/-- Finite powers, including rank zero, are the existing categorical finite products.
Source: blueprint Local models (blueprint: lem-sfb-scalar-model-finite-flat-resolution). -/
abbrev scalarModelPower {B : Sheaf J CommRingCat.{r}}
    (N : scalarModelModules B) (n : ℕ) :=
  ∏ᶜ (fun _ : Fin n ↦ N)

/-- The two-term complex is Mathlib's double complex in precisely degrees -1 and 0.
Source: blueprint Local models (blueprint: lem-sfb-scalar-model-finite-flat-resolution). -/
abbrev scalarModelTwoTerm {A : Type uA} [Category.{vA} A] [HasZeroMorphisms A]
    [HasZeroObject A] {X Y : A} (f : X ⟶ Y) : CochainComplex A ℤ :=
  HomologicalComplex.double f (by decide : (ComplexShape.up ℤ).Rel (-1) 0)

variable [HasSheafify J CommRingCat.{r}] [J.WEqualsLocallyBijective CommRingCat.{r}]
  [HasSheafify J RingCat.{r}] [J.WEqualsLocallyBijective RingCat.{r}]

/-- The scalar model is the existing sheafified change of rings applied to the constant
module sheaf. Thus it is B tensor over R_C with P_C, with its B-module structure.
Source: Stacks 03EK; blueprint Local models
(blueprint: lem-sfb-scalar-model-finite-flat-resolution). -/
def scalarModel (R : Type r) [CommRing R] {B : Sheaf J CommRingCat.{r}}
    (α : independentConstantRing J R ⟶ B) (P : ModuleCat.{r} R) : scalarModelModules B :=
  changeOfRingsOfUniverses.{v, u, r, r} α
    ((commutativeConstantModuleIndependent.{u, v, r} J R).obj P)

section ScalarModelProof

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
open HomologicalComplex
open scoped ChangeOfRings

/-- Sectionwise scalar extension, with its actual functorial maps. -/
private def scalarExtensionPresheafFunctor {A B : Sheaf J CommRingCat.{r}} (α : A ⟶ B) :
    scalarModelModules A ⥤ PresheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj where
  obj M := changeOfRingsPresheafOfUniverses α M
  map f :=
    { app U := (ModuleCat.extendScalars (α.hom.app U).hom).map (f.val.app U)
      naturality := changeOfRingsHom_naturalityOfUniverses α _ f }
  map_id M := by
    ext U : 1
    exact (ModuleCat.extendScalars (α.hom.app U).hom).map_id _
  map_comp f g := by
    ext U : 1
    exact (ModuleCat.extendScalars (α.hom.app U).hom).map_comp _ _

private theorem scalarExtensionPresheafFunctor_additive
    {A B : Sheaf J CommRingCat.{r}} (α : A ⟶ B) :
    (scalarExtensionPresheafFunctor α).Additive := by
  constructor
  intro M N f g
  ext U : 1
  let := (α.hom.app U).hom.toAlgebra
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change (1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (α.hom.app U).hom]
    (f.val.app U x + g.val.app U x) = _
  exact TensorProduct.tmul_add _ _ _

attribute [local instance] scalarExtensionPresheafFunctor_additive

private def scalarExtensionFunctor {A B : Sheaf J CommRingCat.{r}} (α : A ⟶ B) :
    scalarModelModules A ⥤ scalarModelModules B :=
  scalarExtensionPresheafFunctor α ⋙
    PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B) (𝟙 _)

private theorem scalarExtensionFunctor_additive
    {A B : Sheaf J CommRingCat.{r}} (α : A ⟶ B) :
    (scalarExtensionFunctor α).Additive := by
  have : (PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B) (𝟙 _)).Additive := by
    apply leftExactFunctor_le_additiveFunctor _ _
    rw [leftExactFunctor_iff]
    infer_instance
  unfold scalarExtensionFunctor
  infer_instance

attribute [local instance] scalarExtensionFunctor_additive

/-- Multiplication identifies scalar extension of the rank-one free module with the unit. -/
private def scalarExtensionUnitIso {A B : Sheaf J CommRingCat.{r}} (α : A ⟶ B) :
    (scalarExtensionFunctor α).obj
      (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) ≅
        unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) := by
  let e : changeOfRingsPresheafOfUniverses α
      (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) ≅
        (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)).val :=
    PresheafOfModules.isoMk (fun U ↦ by
      letI := (α.hom.app U).hom.toAlgebra
      exact (TensorProduct.AlgebraTensorModule.rid
        (A.obj.obj U) (B.obj.obj U) (B.obj.obj U)).toModuleIso) (by
      intro U V f
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      change A.obj.obj U at x
      let := (α.hom.app U).hom.toAlgebra
      let := (α.hom.app V).hom.toAlgebra
      change (TensorProduct.AlgebraTensorModule.rid
        (A.obj.obj V) (B.obj.obj V) (B.obj.obj V))
          (changeOfRingsMapOfUniverses.{v, u, r, r} α
            (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) f
              ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (α.hom.app U).hom] x)) = _
      rw [changeOfRingsMap_tmulOfUniverses, map_one]
      change (A.obj.map f x) • (1 : B.obj.obj V) =
        B.obj.map f (x • (1 : B.obj.obj U))
      simp only [Algebra.smul_def, mul_one]
      exact NatTrans.naturality_apply α.hom f x)
  exact (PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B) (𝟙 _)).mapIso e ≪≫
      (asIso (PresheafOfModules.sheafificationAdjunction.{r}
        (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B) (𝟙 _)).counit).app
          (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))

set_option backward.isDefEq.respectTransparency false in
private def constantUnitSeed (R : Type r) [CommRing R] :
    (siteConstantModulePresheafIndependent (C := C) R).obj (ModuleCat.of R R) ⟶
      (PresheafOfModules.restrictScalars (independentConstantRingUnit J R)).obj
        (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (independentConstantRing J R))).val where
  app U := ModuleCat.ofHom
    (Y := ((PresheafOfModules.restrictScalars (independentConstantRingUnit J R)).obj
      (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (independentConstantRing J R))).val).obj U)
    { toFun := (independentConstantRingUnit J R).app U
      map_add' := map_add _
      map_smul' a b := map_mul ((independentConstantRingUnit J R).app U).hom a b }
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (NatTrans.naturality_apply (independentConstantRingUnit J R) f x)

/-- The ring sheafification unit identifies the constant rank-one module with the unit. -/
private def constantUnitIso (R : Type r) [CommRing R] :
    (commutativeConstantModuleIndependent J R).obj (ModuleCat.of R R) ≅
      unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (independentConstantRing J R)) := by
  have := (independentConstantRingUnit_locallyBijective J R).1
  have := (independentConstantRingUnit_locallyBijective J R).2
  let f := (PresheafOfModules.sheafificationHomEquiv
    (F := unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (independentConstantRing J R)))
    (independentConstantRingUnit J R)).symm (constantUnitSeed (J := J) R)
  let φ := (PresheafOfModules.toPresheaf _).map (constantUnitSeed (J := J) R)
  have : Presheaf.IsLocallyInjective J φ :=
    ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J (independentConstantRingUnit J R) x y h⟩
  have : Presheaf.IsLocallySurjective J φ :=
    ⟨fun x ↦ Presheaf.imageSieve_mem J (independentConstantRingUnit J R) x⟩
  have : Presheaf.IsLocallySurjective J
      (toSheafify J
        ((siteConstantModulePresheafIndependent (C := C) R).obj
          (ModuleCat.of R R)).presheaf) := by
    change Presheaf.IsLocallySurjective J
      (toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of R)))
    infer_instance
  have hfac : toSheafify J
      ((siteConstantModulePresheafIndependent (C := C) R).obj (ModuleCat.of R R)).presheaf ≫
        (PresheafOfModules.toPresheaf _).map f.val = φ :=
    congrArg ((PresheafOfModules.toPresheaf _).map)
      ((PresheafOfModules.sheafificationHomEquiv
        (independentConstantRingUnit J R)).apply_symm_apply _)
  have : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map f.val) := by
    exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      J φ hfac
  have : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf _).map f.val) := by
    apply Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac
  have : IsIso ((SheafOfModules.toSheaf _).map f) :=
    (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨‹_›, ‹_›⟩
  have : IsIso f := isIso_of_reflects_iso f (SheafOfModules.toSheaf _)
  exact asIso f

/-- Constant presheaves and module sheafification preserve finite exact sequences. -/
private theorem constantFunctor_exact (R : Type r) [CommRing R] :
    (commutativeConstantModuleIndependent J R).Additive ∧
      PreservesFiniteLimits (commutativeConstantModuleIndependent J R) ∧
      PreservesFiniteColimits (commutativeConstantModuleIndependent J R) := by
  let P := siteConstantModulePresheafIndependent (C := C) R
  have : PreservesFiniteLimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦ hc)⟩
  have : PreservesFiniteColimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X ↦ hc)⟩
  have := (independentConstantRingUnit_locallyBijective J R).1
  have := (independentConstantRingUnit_locallyBijective J R).2
  change (P ⋙ PresheafOfModules.sheafification (independentConstantRingUnit J R)).Additive ∧
    PreservesFiniteLimits (P ⋙ PresheafOfModules.sheafification (independentConstantRingUnit J R)) ∧
    PreservesFiniteColimits (P ⋙ PresheafOfModules.sheafification (independentConstantRingUnit J R))
  have : PreservesFiniteLimits
      (P ⋙ PresheafOfModules.sheafification (independentConstantRingUnit J R)) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits
      (P ⋙ PresheafOfModules.sheafification (independentConstantRingUnit J R)) :=
    comp_preservesFiniteColimits _ _
  refine ⟨?_, inferInstance, inferInstance⟩
  apply leftExactFunctor_le_additiveFunctor _ _
  rw [leftExactFunctor_iff]
  infer_instance

private def scalarModelFunctor (R : Type r) [CommRing R] {B : Sheaf J CommRingCat.{r}}
    (α : independentConstantRing J R ⟶ B) : ModuleCat.{r} R ⥤ scalarModelModules B :=
  commutativeConstantModuleIndependent J R ⋙ scalarExtensionFunctor α

/-- Additivity carries finite powers of the scalar ring to finite powers of the unit. -/
private def scalarModelFreeIso (R : Type r) [CommRing R] {B : Sheaf J CommRingCat.{r}}
    (α : independentConstantRing J R ⟶ B) (n : ℕ) :
    scalarModel R α (ModuleCat.of R (Fin n → R)) ≅
      scalarModelPower (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) n := by
  have := (constantFunctor_exact (J := J) R).1
  have : (scalarModelFunctor R α).Additive := by
    unfold scalarModelFunctor
    infer_instance
  let e : (scalarModelFunctor R α).obj (ModuleCat.of R R) ≅
      unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) :=
    (scalarExtensionFunctor α).mapIso (constantUnitIso (J := J) R) ≪≫
      scalarExtensionUnitIso α
  exact (scalarModelFunctor R α).mapIso
    (ModuleCat.piIsoPi (fun _ : Fin n ↦ ModuleCat.of R R)).symm ≪≫
      PreservesProduct.iso (scalarModelFunctor R α) (fun _ : Fin n ↦ ModuleCat.of R R) ≪≫
      Pi.mapIso (fun _ : Fin n ↦ e)

private theorem power_zero_isZero {B : Sheaf J CommRingCat.{r}}
    (N : scalarModelModules B) : IsZero (scalarModelPower N 0) := by
  rw [IsZero.iff_id_eq_zero]
  apply Pi.hom_ext
  intro j
  exact Fin.elim0 j

private theorem single_finiteFree_kflat (B : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (scalarModelModules B)] (n : ℕ) (M : scalarModelModules B)
    (e : M ≅ scalarModelPower
      (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) n) :
    CochainComplex.IsKFlatIndependentCoefficients
      ((CochainComplex.singleFunctor (scalarModelModules B) 0).obj M) := by
  classical
  let K := (CochainComplex.singleFunctor (scalarModelModules B) 0).obj M
  let rank : ℤ → ℕ := fun i ↦ if i = 0 then n else 0
  have hbound (i : ℤ) (hi : (0 : ℤ) < i) : IsZero (K.X i) :=
    HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have hrank (i : ℤ) (hi : (0 : ℤ) < i) : rank i = 0 := by
    simp only [rank, if_neg (ne_of_gt hi)]
  have theta (i : ℤ) : K.X i ≅
      FiniteFreeResolution.power B
        (MonoidalCategory.tensorUnit (scalarModelModules B)) (rank i) := by
    by_cases hi : i = 0
    · subst i
      exact HomologicalComplex.singleObjXSelf _ _ _ ≪≫ e
    · dsimp only [rank]
      rw [if_neg hi]
      exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).iso
        (power_zero_isZero (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)))
  obtain ⟨_, hK, _⟩ :=
    FiniteFreeResolution.finiteFreeResolution_tensor B K 0 hbound rank hrank theta
  exact hK

/-- After forgetting scalars, extension is tensor by the restricted target ring. -/
private def scalarExtensionForgetIso {A B : Sheaf J CommRingCat.{r}} (α : A ⟶ B) :
    scalarExtensionFunctor α ⋙ toSheaf _ ≅
      siteSheafTensorRight
        ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
          (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))) ⋙ toSheaf _ := by
  let F := scalarExtensionPresheafFunctor α ⋙ PresheafOfModules.toPresheaf _
  let G := SheafOfModules.forget.{r}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A) ⋙ siteTensorRight
    ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
      (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))).val ⋙
        PresheafOfModules.toPresheaf _
  let e : F ≅ G := NatIso.ofComponents (fun M ↦
    NatIso.ofComponents (fun U ↦ by
      letI : Module (A.obj.obj U) (B.obj.obj U) :=
        Module.compHom (B.obj.obj U) (α.hom.app U).hom
      exact (TensorProduct.comm (A.obj.obj U) (B.obj.obj U)
        (M.val.obj U)).toAddEquiv.toAddCommGrpIso) (by
        intro U V f
        let : Module (A.obj.obj U) (B.obj.obj U) :=
          Module.compHom (B.obj.obj U) (α.hom.app U).hom
        let : Module (A.obj.obj V) (B.obj.obj V) :=
          Module.compHom (B.obj.obj V) (α.hom.app V).hom
        apply AddCommGrpCat.hom_ext
        ext z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add z w hz hw => simp only [map_add, hz, hw]
        | tmul s x =>
          change TensorProduct.comm (A.obj.obj V) (B.obj.obj V) (M.val.obj V)
            (changeOfRingsMapOfUniverses.{v, u, r, r} α M f
              (s ⊗ₜ[A.obj.obj U, (α.hom.app U).hom] x)) =
                M.val.map f x ⊗ₜ[A.obj.obj V] B.obj.map f s
          rw [changeOfRingsMap_tmulOfUniverses]
          rfl)) (by
      intro M N f
      apply NatTrans.ext
      funext U
      apply AddCommGrpCat.hom_ext
      ext z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp only [map_add, hz, hw]
      | tmul s x => rfl)
  exact Functor.isoWhiskerRight e (presheafToSheaf J AddCommGrpCat.{r})

/-- Flatness makes extension exact; the additive sheaf forgetful functor reflects this. -/
private theorem scalarExtension_exact {A B : Sheaf J CommRingCat.{r}} (α : A ⟶ B)
    (hB : IsFlatOnSite (R := A)
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
        (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)))) :
    PreservesFiniteLimits (scalarExtensionFunctor α) ∧
      PreservesFiniteColimits (scalarExtensionFunctor α) := by
  let T := siteSheafTensorRight
    ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
      (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)))
  have : PreservesFiniteLimits T := hB.1
  have : PreservesFiniteColimits T := hB.2
  have : PreservesFiniteLimits (T ⋙ toSheaf.{r} _) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (T ⋙ toSheaf.{r} _) := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits (scalarExtensionFunctor α ⋙ toSheaf.{r} _) :=
    preservesFiniteLimits_of_natIso (scalarExtensionForgetIso α).symm
  have : PreservesFiniteColimits (scalarExtensionFunctor α ⋙ toSheaf.{r} _) :=
    preservesFiniteColimits_of_natIso (scalarExtensionForgetIso α).symm
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ (toSheaf _),
    preservesFiniteColimits_of_reflects_of_preserves _ (toSheaf _)⟩

/-- A PID basis of the scalar kernel gives the exact finite free sheaf presentation. -/
private theorem scalarModel_shortExact_dvr
    (R : Type r) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (B : Sheaf J CommRingCat.{r}) (α : independentConstantRing J R ⟶ B)
    (P : ModuleCat.{r} R) [Module.FinitePresentation R P]
    (hB : IsFlatOnSite (R := independentConstantRing J R)
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
        (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)))) :
    ∃ (m n : ℕ)
      (f : scalarModelPower
          (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) m ⟶
        scalarModelPower (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) n)
      (g : scalarModelPower
          (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) n ⟶
        scalarModel R α P) (h : f ≫ g = 0),
      (ShortComplex.mk f g h).ShortExact := by
  obtain ⟨n, _, q, _, hq, _⟩ := Module.FinitePresentation.exists_fin' R P
  obtain ⟨m, b⟩ := Submodule.basisOfPid (Pi.basisFun R (Fin n)) (LinearMap.ker q)
  let a := (LinearMap.ker q).subtype.comp b.equivFun.symm.toLinearMap
  have ha : Function.Injective a := Subtype.val_injective.comp b.equivFun.symm.injective
  have haq : q.comp a = 0 := by
    apply LinearMap.ext
    intro x
    exact (b.equivFun.symm x).property
  let S := ShortComplex.moduleCatMk a q haq
  have hS : S.ShortExact := by
    have : Mono S.f := (ModuleCat.mono_iff_injective _).2 ha
    have : Epi S.g := (ModuleCat.epi_iff_surjective _).2 hq
    refine ⟨(ShortComplex.moduleCat_exact_iff _).2 ?_⟩
    intro x hx
    refine ⟨b.equivFun ⟨x, hx⟩, ?_⟩
    change (b.equivFun.symm (b.equivFun ⟨x, hx⟩)).val = x
    simp
  have := (constantFunctor_exact (J := J) R).1
  have := (constantFunctor_exact (J := J) R).2.1
  have := (constantFunctor_exact (J := J) R).2.2
  have := (scalarExtension_exact α hB).1
  have := (scalarExtension_exact α hB).2
  let F := scalarModelFunctor R α
  have : PreservesFiniteLimits F := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits F := comp_preservesFiniteColimits _ _
  have : F.Additive := by unfold F scalarModelFunctor; infer_instance
  let em := scalarModelFreeIso R α m
  let en := scalarModelFreeIso R α n
  let f := em.inv ≫ F.map S.f ≫ en.hom
  let g := en.inv ≫ F.map S.g
  have hfg : f ≫ g = 0 := by
    dsimp only [f, g]
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
      ← F.map_comp, S.zero, F.map_zero, comp_zero]
  let T := ShortComplex.mk f g hfg
  have e : S.map F ≅ T := ShortComplex.isoMk em en (Iso.refl _)
    (by simp [T, f]) (by simp [T, g])
  exact ⟨m, n, f, g, hfg, ShortComplex.shortExact_of_iso e (hS.map_of_exact F)⟩

/-- The two-term complex of a short exact sequence resolves its cokernel. -/
private theorem twoTerm_augmentation {A : Type uA} [Category.{vA} A] [Abelian A]
    (S : ShortComplex A) (hS : S.ShortExact) :
    ∃ ε : scalarModelTwoTerm S.f ⟶ (CochainComplex.singleFunctor A 0).obj S.X₃,
      QuasiIso ε := by
  classical
  let K := scalarModelTwoTerm S.f
  let L := (CochainComplex.singleFunctor A 0).obj S.X₃
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 S.X₃
  let em := HomologicalComplex.doubleXIso₀ S.f (by decide : (ComplexShape.up ℤ).Rel (-1) 0)
  let en := HomologicalComplex.doubleXIso₁ S.f (by decide : (ComplexShape.up ℤ).Rel (-1) 0)
    (by decide : (-1 : ℤ) ≠ 0)
  have hz (i : ℤ) (hm : i ≠ -1) (h0 : i ≠ 0) : IsZero (K.X i) :=
    HomologicalComplex.isZero_double_X _ _ i hm h0
  have hL (i : ℤ) (hi : i ≠ 0) : IsZero (L.X i) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 S.X₃ i hi
  let ε : K ⟶ L := HomologicalComplex.mkHomFromDouble _ (by decide) 0 (S.g ≫ e.inv)
    (by rw [zero_comp, ← Category.assoc, S.zero, zero_comp])
    (by intro i hi; exact (hL i (by simp only [ComplexShape.up_Rel] at hi; omega)).eq_of_tgt _ _)
  have hε0 : ε.f 0 ≫ e.hom = en.hom ≫ S.g := by simp [ε, en]
  have hεi (i : ℤ) (hi : i ≠ 0) : ε.f i = 0 := (hL i hi).eq_of_tgt _ _
  have := hS.mono_f
  have := hS.epi_g
  have hmono : Mono (K.d (-1) 0) := by
    dsimp [K, scalarModelTwoTerm]
    rw [HomologicalComplex.double_d _ _ (by decide)]
    infer_instance
  refine ⟨ε, ?_⟩
  rw [quasiIso_iff]
  intro i
  by_cases hi : i = 0
  · subst i
    rw [quasiIsoAt_iff' ε (-1) 0 1 (by simp) (by simp)]
    apply (ShortComplex.quasiIso_iff_of_zeros' _
      ((hz 1 (by omega) (by omega)).eq_of_tgt _ _)
      ((hL (-1) (by omega)).eq_of_src _ _)
      ((hL 1 (by omega)).eq_of_tgt _ _)).2
    have heq : K.d (-1) 0 ≫ ε.f 0 = 0 := by
      rw [← ε.comm]
      simp [hεi (-1) (by omega)]
    let T := ShortComplex.mk (K.d (-1) 0) (ε.f 0) heq
    let iso : T ≅ S := ShortComplex.isoMk em en e
      (by dsimp [T, K, em, en, scalarModelTwoTerm]
          rw [HomologicalComplex.double_d _ _ (by decide)]; simp) hε0.symm
    have hs : T.Exact := (ShortComplex.exact_iff_of_iso iso).2 hS.exact
    have : Epi (ε.f 0) := by
      have : Epi (ε.f 0 ≫ e.hom) := by rw [hε0]; infer_instance
      exact (epi_comp_iff_of_isIso (ε.f 0) e.hom).1 inferInstance
    exact ⟨hs, show Epi (ε.f 0) from inferInstance⟩
  · have hLex : L.ExactAt i := HomologicalComplex.ExactAt.of_isZero (hL i hi)
    rw [quasiIsoAt_iff_exactAt' ε i hLex]
    by_cases hm : i = -1
    · subst i
      rw [HomologicalComplex.exactAt_iff' K (-2) (-1) 0 (by simp) (by simp)]
      apply (ShortComplex.exact_iff_mono _ ((hz (-2) (by omega) (by omega)).eq_of_src _ _)).2
      exact hmono
    · exact HomologicalComplex.ExactAt.of_isZero (hz i hm hi)

/-- The finite-free comparison computes tensor using this same two-term differential. -/
private theorem twoTerm_finiteFree_tensor (B : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (scalarModelModules B)] (m n : ℕ)
    (f : scalarModelPower
        (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) m ⟶
      scalarModelPower (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) n)
    (M : scalarModelModules B)
    (ε : scalarModelTwoTerm f ⟶ (CochainComplex.singleFunctor _ 0).obj M)
    [QuasiIso ε] :
    (scalarModelTwoTerm f).IsKFlatIndependentCoefficients ∧
      ∀ N : scalarModelModules B,
        ∃ (em : (siteSheafTensorRight N).obj
            (scalarModelPower (unit ((sheafCompose J
              (forget₂ CommRingCat RingCat)).obj B)) m) ≅ scalarModelPower N m)
          (en : (siteSheafTensorRight N).obj
            (scalarModelPower (unit ((sheafCompose J
              (forget₂ CommRingCat RingCat)).obj B)) n) ≅ scalarModelPower N n),
          Nonempty ((siteDerivedTensorIndependentCoefficients J B).obj
            (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj M),
             DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj N)) ≅
            DerivedCategory.Q.obj (scalarModelTwoTerm
              (em.inv ≫ (siteSheafTensorRight N).map f ≫ en.hom))) := by
  classical
  let K := scalarModelTwoTerm f
  let rank : ℤ → ℕ := fun i ↦ if i = -1 then m else if i = 0 then n else 0
  have hbound (i : ℤ) (hi : (0 : ℤ) < i) : IsZero (K.X i) :=
    HomologicalComplex.isZero_double_X _ _ i (by omega) (by omega)
  have hrank (i : ℤ) (hi : (0 : ℤ) < i) : rank i = 0 := by
    simp [rank, ne_of_gt hi, show i ≠ -1 by omega]
  have theta (i : ℤ) : K.X i ≅ FiniteFreeResolution.power B
      (MonoidalCategory.tensorUnit (scalarModelModules B)) (rank i) := by
    by_cases hm : i = -1
    · subst i
      exact HomologicalComplex.doubleXIso₀ _ _
    · by_cases hn : i = 0
      · subst i
        exact HomologicalComplex.doubleXIso₁ _ _ (by decide)
      · dsimp only [rank]
        rw [if_neg hm, if_neg hn]
        exact (HomologicalComplex.isZero_double_X _ _ i hm hn).iso
          (power_zero_isZero (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)))
  obtain ⟨_, hK, c, _⟩ :=
    FiniteFreeResolution.finiteFreeResolution_tensor B K 0 hbound rank hrank theta
  refine ⟨hK, ?_⟩
  intro N
  let T := siteSheafTensorRight N
  let ti : T ≅ (SheafOfModules.KFlatFixedTensor.ordinaryTensor B).flip.obj N :=
    siteSheafTensorRightIso B N
  have : T.Additive := Functor.additive_of_iso ti.symm
  let ep (s : ℕ) : T.obj (scalarModelPower
      (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) s) ≅
        scalarModelPower N s :=
    PreservesProduct.iso T _ ≪≫ Pi.mapIso (fun _ : Fin s ↦
      ti.app _ ≪≫ MonoidalCategory.leftUnitor N)
  let em := ep m
  let en := ep n
  let a : Arrow.mk (T.map f) ≅ Arrow.mk (em.inv ≫ T.map f ≫ en.hom) :=
    Arrow.isoMk em en (by simp)
  let d := (HomologicalComplex.doubleFunctor (scalarModelModules B)
    (by decide : (ComplexShape.up ℤ).Rel (-1) 0) (by decide : (-1 : ℤ) ≠ 0)).mapIso a
  let tensorIso := CochainComplex.mapBifunctorSingle₂Iso
    (SheafOfModules.KFlatFixedTensor.ordinaryTensor B) N K ≪≫
      (NatIso.mapHomologicalComplex ti.symm (ComplexShape.up ℤ)).app K ≪≫
        HomologicalComplex.mapHomologicalComplexObjDoubleIso f
          (by decide : (ComplexShape.up ℤ).Rel (-1) 0) (by decide : (-1 : ℤ) ≠ 0) T ≪≫ d
  let de := ((SheafOfModules.KFlatFixedTensor.derivedTensor B).mapIso
    (asIso (DerivedCategory.Q.map ε))).app (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor _ 0).obj N))
  exact ⟨em, en, ⟨de.symm ≪≫ (c.app _).symm ≪≫ DerivedCategory.Q.mapIso tensorIso⟩⟩

end ScalarModelProof

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Over a DVR the flat scalar model has a finite free length-one resolution and that
very two-term K-flat complex computes tensor with every module sheaf.

Source: blueprint main-20261015, ctf-equals-bc proof, Local models; Stacks 03EI,
06YQ, 06YS, 06YP and 06YU (blueprint: lem-sfb-scalar-model-finite-flat-resolution).

Proof:
1. Mathlib's finite presentation and `Submodule.basisOfPid` construct a short exact
scalar sequence with finite free source terms.
2. Constant presheaves and module sheafification are exact. The ring sheafification
unit identifies the constant regular module with the sheaf unit. Scalar extension
carries the unit to B by multiplication and all finite powers to powers of B by
additivity. Its underlying additive functor is tensor by restricted B, hence is exact
under the given flatness hypothesis. Transport the short exact sequence.
3. Augment its double complex by the quotient map. Exactness and the endpoint mono
and epi show that this is a quasi-isomorphism, degree by degree.
4. Apply the stated finite-free resolution tensor comparison for K-flatness and the
derived tensor isomorphism. Tensoring the double complex gives the double of the
mapped differential. The finite-power and unit isomorphisms transport its differential
exactly to the one in the conclusion, including empty powers. -/
theorem scalarModel_finite_flat_resolution_dvr
    (R : Type r) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (B : Sheaf J CommRingCat.{r}) (α : independentConstantRing J R ⟶ B)
    (P : ModuleCat.{r} R) [Module.FinitePresentation R P]
    (hB : IsFlatOnSite (R := independentConstantRing J R)
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map α)).obj
        (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj B))))
    [HasDerivedCategory.{w} (scalarModelModules B)] :
    ∃ (m n : ℕ)
      (f : scalarModelPower
          (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj B)) m ⟶
        scalarModelPower (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj B)) n)
      (g : scalarModelPower
          (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj B)) n ⟶
        scalarModel R α P) (h : f ≫ g = 0),
      (ShortComplex.mk f g h).ShortExact ∧
      ∃ ε : scalarModelTwoTerm f ⟶
          (CochainComplex.singleFunctor (scalarModelModules B) 0).obj (scalarModel R α P),
        QuasiIso ε ∧ CochainComplex.IsKFlatIndependentCoefficients (scalarModelTwoTerm f) ∧
        ∀ N : scalarModelModules B,
          ∃ (em : (siteSheafTensorRight N).obj
              (scalarModelPower (unit ((sheafCompose J
                (forget₂ CommRingCat.{r} RingCat.{r})).obj B)) m) ≅ scalarModelPower N m)
            (en : (siteSheafTensorRight N).obj
              (scalarModelPower (unit ((sheafCompose J
                (forget₂ CommRingCat.{r} RingCat.{r})).obj B)) n) ≅ scalarModelPower N n),
            Nonempty ((siteDerivedTensorIndependentCoefficients J B).obj
              (DerivedCategory.Q.obj ((CochainComplex.singleFunctor
                (scalarModelModules B) 0).obj (scalarModel R α P)),
               DerivedCategory.Q.obj ((CochainComplex.singleFunctor
                (scalarModelModules B) 0).obj N)) ≅
              DerivedCategory.Q.obj (scalarModelTwoTerm
                (em.inv ≫ (siteSheafTensorRight N).map f ≫ en.hom))) := by
  obtain ⟨m, n, f, g, hfg, hS⟩ := scalarModel_shortExact_dvr R B α P hB
  obtain ⟨ε, hε⟩ := twoTerm_augmentation (ShortComplex.mk f g hfg) hS
  have := hε
  obtain ⟨hK, hN⟩ := twoTerm_finiteFree_tensor B m n f _ ε
  exact ⟨m, n, f, g, hfg, hS, ε, hε, hK, hN⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Over a field the scalar model is finite free and its derived tensor is a finite
power in degree zero, without any flatness hypothesis on B over the constant ring.

Source: blueprint main-20261015, ctf-equals-bc proof, Local models; Stacks 03EI,
06YQ, 06YS, 06YP and 06YU (blueprint: lem-sfb-scalar-model-finite-flat-resolution).

Proof:
1. `Module.finBasis` identifies the finitely presented vector space with R^n.
2. Map this isomorphism through the actual scalar-model functor. Additivity and the
rank-one unit comparison identify the resulting model with B^n; no flatness is used.
3. Apply the finite-free tensor theorem to its degree-zero single complex for
K-flatness, and its degree-zero augmentation formula for tensor with N[0]. -/
theorem scalarModel_finite_free_field
    (R : Type r) [Field R] (B : Sheaf J CommRingCat.{r})
    (α : independentConstantRing J R ⟶ B)
    (P : ModuleCat.{r} R) [Module.FinitePresentation R P]
    [HasDerivedCategory.{w} (scalarModelModules B)] :
    ∃ n : ℕ,
      Nonempty (scalarModel R α P ≅
        scalarModelPower (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj B)) n) ∧
      CochainComplex.IsKFlatIndependentCoefficients
        ((CochainComplex.singleFunctor (scalarModelModules B) 0).obj (scalarModel R α P)) ∧
      ∀ N : scalarModelModules B,
        Nonempty ((siteDerivedTensorIndependentCoefficients J B).obj
          (DerivedCategory.Q.obj ((CochainComplex.singleFunctor
            (scalarModelModules B) 0).obj (scalarModel R α P)),
           DerivedCategory.Q.obj ((CochainComplex.singleFunctor
            (scalarModelModules B) 0).obj N)) ≅
          DerivedCategory.Q.obj ((CochainComplex.singleFunctor
            (scalarModelModules B) 0).obj (scalarModelPower N n))) := by
  let n := Module.finrank R P
  let e : scalarModel R α P ≅ scalarModelPower
      (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) n :=
    (scalarModelFunctor R α).mapIso (Module.finBasis R P).equivFun.toModuleIso ≪≫
      scalarModelFreeIso R α n
  refine ⟨n, ⟨e⟩, single_finiteFree_kflat B n _ e, ?_⟩
  exact (FiniteFreeResolution.finiteFree_iso_augmentation B n _ e.symm).2

end SheafOfModules
