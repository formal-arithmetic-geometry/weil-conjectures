/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Subobject.Limits
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Paper.ExactScalarPeriodicResolution
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-! # The constant periodic resolution and its nonzero quotient

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-def-localizing-closure-ctf-equals-bc.proof.md, "The examples";
Stacks Project, Tags 093J, 03CY and 06YQ.
(blueprint: lem-sfb-constant-periodic-resolution-nonzero).

The resolution is specified by its term identifications and all its differentials.
The augmentation is fixed in every degree, including its quotient component in degree zero.
The sized constant-module helpers belong to this realization; the landed general
constant-module dependency and its record are preserved without changes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe r u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  (J : GrothendieckTopology C) (Λ : Type w) [CommRing Λ]

/-- Ring sheafification transported from the small model in the coefficient universe.
Source: Stacks Tag 03CY (blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
instance siteConstantSizedRingSheafify : HasSheafify J RingCat.{w} :=
  hasSheafifyEssentiallySmallSite J RingCat.{w}

/-- Commutative ring sheafification on the same small model.
Source: Stacks Tag 03CY (blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
instance siteConstantSizedCommRingSheafify : HasSheafify J CommRingCat.{w} :=
  hasSheafifyEssentiallySmallSite J CommRingCat.{w}

/-- Limits needed to transport ring sheafification from the small model.
Source: Stacks Tag 03CY (blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
instance siteConstantSizedRingStructuredLimits :
    ∀ X : Cᵒᵖ, Limits.HasLimitsOfShape
      (StructuredArrow X (equivSmallModel.{w} C).inverse.op) RingCat.{w} :=
  fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{w} _ _

/-- The analogous limits for commutative rings.
Source: Stacks Tag 03CY (blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
instance siteConstantSizedCommRingStructuredLimits :
    ∀ X : Cᵒᵖ, Limits.HasLimitsOfShape
      (StructuredArrow X (equivSmallModel.{w} C).inverse.op) CommRingCat.{w} :=
  fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{w} _ _

/-- The local description of ring sheafification transported from the small model.
Source: Stacks Tag 03CY (blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
instance siteConstantSizedRingLocallyBijective : J.WEqualsLocallyBijective RingCat.{w} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J

/-- The constant module presheaf, with the original scalar action and identity restrictions.
Source: Stacks Tags 03CY and 093T (blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
def siteConstantModulePresheafSized : ModuleCat.{w} Λ ⥤
    PresheafOfModules.{w} ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) where
  obj M := { obj := fun _ ↦ M, map := fun _ ↦ ModuleCat.ofHom LinearMap.id }
  map f := { app := fun _ ↦ f }

/-- Module sheafification of the constant module presheaf over the constant ring sheaf.
Source: Stacks Tags 03CY and 093T (blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
def siteConstantModuleFunctorSized : ModuleCat.{w} Λ ⥤ SheafOfModules.{w}
    ((constantSheaf J RingCat.{w}).obj (RingCat.of Λ)) :=
  siteConstantModulePresheafSized (C := C) Λ ⋙ PresheafOfModules.sheafification
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))

set_option backward.isDefEq.respectTransparency false in
/-- The canonical coefficient isomorphism, commuting sheafification with forgetting
commutativity. Source: Stacks Tag 03CY (blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
def siteConstantSizedRingIso :
    (constantSheaf J RingCat.{w}).obj (RingCat.of Λ) ≅
      (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj
        ((constantSheaf J CommRingCat.{w}).obj (CommRingCat.of Λ)) :=
  letI : ((equivSmallModel.{w} C).inverse.inducedTopology J).PreservesSheafification
      (forget₂ CommRingCat.{w} RingCat.{w}) :=
    GrothendieckTopology.instPreservesSheafification
      ((equivSmallModel.{w} C).inverse.inducedTopology J)
      (forget₂ CommRingCat.{w} RingCat.{w})
      (FD := fun A B : CommRingCat.{w} ↦ A →+* B)
      (CD := fun A : CommRingCat.{w} ↦ A)
      (FE := fun A B : RingCat.{w} ↦ A →+* B)
      (CE := fun A : RingCat.{w} ↦ A)
  letI : J.PreservesSheafification (forget₂ CommRingCat.{w} RingCat.{w}) :=
    GrothendieckTopology.PreservesSheafification.transport (A := CommRingCat.{w}) J
      ((equivSmallModel.{w} C).inverse.inducedTopology J)
      (equivSmallModel.{w} C).inverse RingCat.{w}
      (forget₂ CommRingCat.{w} RingCat.{w})
  (sheafComposeNatIso J (forget₂ CommRingCat.{w} RingCat.{w})
    (sheafificationAdjunction J CommRingCat.{w})
    (sheafificationAdjunction J RingCat.{w})).app
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of Λ))

/-- The same constant module sheaf over the underlying constant commutative ring sheaf.
Source: Stacks Tags 03CY and 093T (blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
def siteConstantCommModuleFunctorSized : ModuleCat.{w} Λ ⥤ SheafOfModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj
      ((constantSheaf J CommRingCat.{w}).obj (CommRingCat.of Λ))) :=
  siteConstantModuleFunctorSized J Λ ⋙
    SheafOfModules.pushforward (F := 𝟭 C) (siteConstantSizedRingIso J Λ).inv

/-- The additive sheafification unit after the canonical coefficient isomorphism.
Source: Stacks Tag 03CY (blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
def siteConstantCommModuleUnitSized (M : ModuleCat.{w} Λ) :
    (Functor.const Cᵒᵖ).obj ((forget₂ (ModuleCat Λ) AddCommGrpCat).obj M) ⟶
      ((siteConstantCommModuleFunctorSized J Λ).obj M).val.presheaf :=
  toSheafify J ((siteConstantModulePresheafSized (C := C) Λ).obj M).presheaf

set_option backward.isDefEq.respectTransparency false in
private def sizedUnitMap :
    (siteConstantModuleFunctorSized J Λ).obj (ModuleCat.of Λ Λ) ⟶
      SheafOfModules.unit ((constantSheaf J RingCat.{w}).obj (RingCat.of Λ)) :=
  (PresheafOfModules.sheafificationHomEquiv
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))).symm
    { app := fun U ↦ ModuleCat.ofHom
        (Y := ((PresheafOfModules.restrictScalars
          (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))).obj
          (SheafOfModules.unit ((constantSheaf J RingCat.{w}).obj (RingCat.of Λ))).val).obj U)
        { toFun := fun x ↦ (toSheafify J
            ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app U x
          map_add' := map_add _
          map_smul' := fun a b ↦ by
            change (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app U (a * b) =
              (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app U a *
              (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app U b
            exact map_mul _ a b }
      naturality := fun {U W} f ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact ConcreteCategory.congr_hom
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).naturality f) x }

set_option backward.isDefEq.respectTransparency false in
private theorem sizedUnitMap_fac :
    toSheafify J ((siteConstantModulePresheafSized (C := C) Λ).obj
        (ModuleCat.of Λ Λ)).presheaf ≫
      ((SheafOfModules.toSheaf _).map (sizedUnitMap J Λ)).hom =
        Functor.whiskerRight
          (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))
          (forget₂ RingCat.{w} AddCommGrpCat.{w}) := by
  change (PresheafOfModules.toPresheaf _).map
    (PresheafOfModules.sheafificationHomEquiv _ (sizedUnitMap J Λ)) = _
  unfold sizedUnitMap
  erw [Equiv.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
private instance sizedUnitMap_isIso : IsIso (sizedUnitMap J Λ) := by
  let f := (SheafOfModules.toSheaf _).map (sizedUnitMap J Λ)
  let η := toSheafify J ((siteConstantModulePresheafSized (C := C) Λ).obj
    (ModuleCat.of Λ Λ)).presheaf
  let α := Functor.whiskerRight
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))
      (forget₂ RingCat.{w} AddCommGrpCat.{w})
  have hi : Presheaf.IsLocallyInjective J α := by
    constructor
    intro U a b hab
    exact Presheaf.equalizerSieve_mem J
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))) a b hab
  have hs : Presheaf.IsLocallySurjective J α := by
    constructor
    intro U a
    exact Presheaf.imageSieve_mem J
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))) a
  let : HasSheafify J AddCommGrpCat.{w} :=
    SheafOfModules.hasSheafify_coefficientUniverse
  let : J.WEqualsLocallyBijective AddCommGrpCat.{w} :=
    SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
  let : Presheaf.IsLocallySurjective J η := by
    dsimp only [η]
    infer_instance
  have : Presheaf.IsLocallyInjective J f.hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J α
      (sizedUnitMap_fac J Λ)
  have : Presheaf.IsLocallySurjective J f.hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J (sizedUnitMap_fac J Λ)
  have : IsIso f := (Sheaf.isLocallyBijective_iff_isIso f).mp ⟨‹_›, ‹_›⟩
  exact isIso_of_reflects_iso (sizedUnitMap J Λ) (SheafOfModules.toSheaf _)

set_option backward.isDefEq.respectTransparency false in
private def sizedUnitIso :
    (siteConstantCommModuleFunctorSized J Λ).obj (ModuleCat.of Λ Λ) ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj
        ((constantSheaf J CommRingCat.{w}).obj (CommRingCat.of Λ))) := by
  letI := sizedUnitMap_isIso J Λ
  let φ := (siteConstantSizedRingIso J Λ).inv
  let η := SheafOfModules.unitToPushforwardObjUnit (F := 𝟭 C) φ
  have : IsIso η := by
    apply (isIso_iff_of_reflects_iso η (SheafOfModules.toSheaf _)).1
    apply (isIso_iff_of_reflects_iso _ (sheafToPresheaf J AddCommGrpCat.{w})).1
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    change IsIso ((forget₂ RingCat.{w} AddCommGrpCat.{w}).map (φ.hom.app U))
    infer_instance
  exact (SheafOfModules.pushforward (F := 𝟭 C) φ).mapIso (asIso (sizedUnitMap J Λ)) ≪≫
    (asIso η).symm

set_option backward.isDefEq.respectTransparency false in
private instance sizedPresheaf_limits :
    PreservesFiniteLimits (siteConstantModulePresheafSized (C := C) Λ) := by
  constructor
  intro K _ _
  constructor
  intro F
  constructor
  intro c hc
  exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦ hc)⟩

set_option backward.isDefEq.respectTransparency false in
private instance sizedPresheaf_colimits :
    PreservesFiniteColimits (siteConstantModulePresheafSized (C := C) Λ) := by
  constructor
  intro K _ _
  constructor
  intro F
  constructor
  intro c hc
  exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X ↦ hc)⟩

set_option backward.isDefEq.respectTransparency false in
private instance sizedConstant_limits :
    PreservesFiniteLimits (siteConstantCommModuleFunctorSized J Λ) := by
  let S := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj
    ((constantSheaf J CommRingCat.{w}).obj (CommRingCat.of Λ))
  have : PreservesFiniteLimits
      (siteConstantCommModuleFunctorSized J Λ ⋙ SheafOfModules.toSheaf S) := by
    change PreservesFiniteLimits
      (siteConstantModulePresheafSized (C := C) Λ ⋙
        PresheafOfModules.sheafification
          (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))) ⋙
        SheafOfModules.toSheaf _)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves
    (siteConstantCommModuleFunctorSized J Λ) (SheafOfModules.toSheaf S)

set_option backward.isDefEq.respectTransparency false in
private instance sizedConstant_colimits :
    PreservesFiniteColimits (siteConstantCommModuleFunctorSized J Λ) := by
  unfold siteConstantCommModuleFunctorSized siteConstantModuleFunctorSized
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private instance sizedConstant_additive :
    (siteConstantCommModuleFunctorSized J Λ).Additive := by
  apply leftExactFunctor_le_additiveFunctor _ _
  rw [leftExactFunctor_iff]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem unit_square_zero_section (S : Sheaf J CommRingCat.{w})
    (f : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj S) ⟶
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (hf : f ≫ f = 0) (U : Cᵒᵖ) :
    (@id (S.obj.obj U) ((SheafOfModules.unitHomEquiv _ f).val U)) *
      (@id (S.obj.obj U) ((SheafOfModules.unitHomEquiv _ f).val U)) = 0 := by
  let l : (S.obj.obj U) →ₗ[S.obj.obj U] (S.obj.obj U) := (f.val.app U).hom
  have hl (a : S.obj.obj U) : l a = a * l 1 := by
    simpa only [smul_eq_mul, mul_one] using l.map_smul a 1
  have hh : l (l 1) = 0 :=
    congrArg (fun g ↦ g.val.app U (1 : S.obj.obj U)) hf
  change l 1 * l 1 = 0
  rw [hl] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
private theorem square_zero_transport
    {D : Type u} [Category.{v} D] [HasZeroMorphisms D] {A B : D}
    (e : A ≅ B) (g : A ⟶ A) (hg : g ≫ g = 0) :
    (e.inv ≫ g ≫ e.hom) ≫ (e.inv ≫ g ≫ e.hom) = 0 := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc g g e.hom, hg, zero_comp, comp_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem cokernel_transport_equation
    {D : Type u} [Category.{v} D] [HasZeroMorphisms D] [HasCokernels D]
    {A B Q : D} (g : A ⟶ A) (f : B ⟶ B) (e₀ : A ≅ B)
    (w : f ≫ e₀.inv = e₀.inv ≫ g) (e : cokernel g ≅ Q) (q : A ⟶ Q)
    (he : cokernel.π g ≫ e.hom = q) :
    cokernel.π f ≫ (cokernel.mapIso (f := f) g e₀.symm e₀.symm w ≪≫ e).hom =
      e₀.inv ≫ q := by
  have hw : f ≫ (e₀.inv ≫ cokernel.π g) = 0 := by
    rw [← Category.assoc, w, Category.assoc, cokernel.condition, comp_zero]
  change cokernel.π f ≫ cokernel.desc f (e₀.inv ≫ cokernel.π g) hw ≫ e.hom = _
  rw [← Category.assoc, cokernel.π_desc, Category.assoc, he]

set_option backward.isDefEq.respectTransparency false in
private theorem exact_transport_endomorphism
    {D : Type u} [Category.{v} D] [Abelian D] {A B : D}
    (g : A ⟶ A) (hg : g ≫ g = 0) (he : (ShortComplex.mk g g hg).Exact)
    (e : A ≅ B) (f : B ⟶ B) (hf : f ≫ f = 0)
    (w : e.hom ≫ f = g ≫ e.hom) : (ShortComplex.mk f f hf).Exact := by
  exact (ShortComplex.exact_iff_of_iso
    (ShortComplex.isoMk (S₁ := ShortComplex.mk g g hg)
      (S₂ := ShortComplex.mk f f hf) e e e w w)).mp he

set_option backward.isDefEq.respectTransparency false in
private theorem kernel_image_of_exact_eq
    {D : Type u} [Category.{v} D] [Abelian D] {A : D}
    (f g : A ⟶ A) (hfg : f = g) (hg : g ≫ g = 0)
    (he : (ShortComplex.mk g g hg).Exact) : kernelSubobject f = imageSubobject f := by
  subst f
  exact ((ShortComplex.exact_iff_image_eq_kernel _).mp he).symm

set_option backward.isDefEq.respectTransparency false in
private theorem periodic_d_identification
    {D : Type u} [Category.{v} D] [HasZeroMorphisms D] [HasZeroObject D]
    {A : D} (f : A ⟶ A) (hf : f ≫ f = 0)
    (i : ℤ) (hi : i < 0) (hi' : i + 1 ≤ 0) :
    (CochainComplex.scalarPeriodic f hf).d i (i + 1) ≫
        (CochainComplex.scalarPeriodicXIso f hf (i + 1) hi').hom =
      (CochainComplex.scalarPeriodicXIso f hf i (le_of_lt hi)).hom ≫ f := by
  dsimp only [CochainComplex.scalarPeriodic, CochainComplex.of_d]
  simp [CochainComplex.scalarPeriodicD, hi, CochainComplex.scalarPeriodicXIso,
    Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_resolution_transport (S : Sheaf J CommRingCat.{w})
    (A Q : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (g : A ⟶ A) (hg : g ≫ g = 0) (hgexact : (ShortComplex.mk g g hg).Exact)
    (e₀ : A ≅ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (e : cokernel g ≅ Q) (q : A ⟶ Q) (he : cokernel.π g ≫ e.hom = q) :
    ∃ P : CochainComplex (SheafOfModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj S)) ℤ,
      ∃ eP : ∀ (i : ℤ), i ≤ 0 → (P.X i ≅ A),
        (∀ i : ℤ, 0 < i → IsZero (P.X i)) ∧
        (∀ (i : ℤ) (hi : i < 0) (hi' : i + 1 ≤ 0),
          P.d i (i + 1) ≫ (eP (i + 1) hi').hom =
            (eP i (le_of_lt hi)).hom ≫ g) ∧
        (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u, v, w, w}
          (J := J) (R := S) (P.X i)) ∧
        (∃ ε : P ⟶ (HomologicalComplex.single _ (.up ℤ) 0).obj Q,
          ε.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).hom =
            (eP 0 (le_refl 0)).hom ≫ q ∧
          (∀ i : ℤ, i ≠ 0 → ε.f i = 0) ∧
          CochainComplex.IsKFlatResolutionIndependentCoefficients.{u, v, w}
            (R := S) ε) := by
  let O := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj S
  let f : SheafOfModules.unit O ⟶ SheafOfModules.unit O :=
    e₀.inv ≫ g ≫ e₀.hom
  let s := (SheafOfModules.unit ((sheafCompose J
    (forget₂ CommRingCat.{w} RingCat.{w})).obj S)).unitHomEquiv f
  have hs : SheafOfModules.exactScalarMultiplication S s = f :=
    (SheafOfModules.unitHomEquiv _).symm_apply_apply f
  have hff : f ≫ f = 0 := square_zero_transport e₀ (g) hg
  have hss (U : Cᵒᵖ) :
      (@id (S.obj.obj U) (s.val U)) * (@id (S.obj.obj U) (s.val U)) = 0 :=
    unit_square_zero_section J S f hff U
  have hfe : (ShortComplex.mk f f hff).Exact := by
    apply exact_transport_endomorphism (g) hg hgexact e₀ f hff
    simp only [f, Iso.hom_inv_id_assoc]
  have hex : kernelSubobject (SheafOfModules.exactScalarMultiplication S s) =
      imageSubobject (SheafOfModules.exactScalarMultiplication S s) :=
    kernel_image_of_exact_eq _ f hs hff hfe
  have hres := SheafOfModules.exact_scalar_periodic_resolution S s hss hex
  let P := SheafOfModules.exactScalarPeriodicComplex S s hss
  let eP := fun i hi ↦ CochainComplex.scalarPeriodicXIso
    (SheafOfModules.exactScalarMultiplication S s)
    (SheafOfModules.exactScalarMultiplication_sq S s hss) i hi ≪≫ e₀.symm
  refine ⟨P, eP, ?_, ?_, hres.2.2.2.2.2.1, ?_⟩
  · intro i hi
    change IsZero (CochainComplex.scalarPeriodicX _ i)
    simp only [CochainComplex.scalarPeriodicX, if_neg (not_le_of_gt hi)]
    exact isZero_zero _
  · intro i hi hi'
    have hd := periodic_d_identification
      (SheafOfModules.exactScalarMultiplication S s)
      (SheafOfModules.exactScalarMultiplication_sq S s hss) i hi hi'
    have hd' := congrArg (fun k ↦ k ≫ e₀.inv) hd
    simpa only [P, SheafOfModules.exactScalarPeriodicComplex, eP, Iso.trans_hom,
      Iso.symm_hom, Category.assoc, hs, f, Iso.hom_inv_id, Category.comp_id] using hd'
  · let ec := cokernel.mapIso (f := SheafOfModules.exactScalarMultiplication S s)
      (g) e₀.symm e₀.symm
      (by rw [hs]
          simp only [f, Iso.symm_hom, Category.assoc, Iso.hom_inv_id,
            Category.comp_id]) ≪≫ e
    have hec : cokernel.π (SheafOfModules.exactScalarMultiplication S s) ≫ ec.hom =
        e₀.inv ≫ q :=
      cokernel_transport_equation (g)
        (SheafOfModules.exactScalarMultiplication S s) e₀ _ e (q) he
    let ε := SheafOfModules.exactScalarPeriodicAugmentation S s hss ≫
      (HomologicalComplex.single _ (.up ℤ) 0).map ec.hom
    refine ⟨ε, ?_, ?_, ?_⟩
    · dsimp only [ε, HomologicalComplex.comp_f]
      rw [HomologicalComplex.single_map_f_self]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      dsimp only [SheafOfModules.exactScalarPeriodicAugmentation,
        CochainComplex.scalarPeriodicAugmentation]
      rw [HomologicalComplex.mkHomToSingle_f]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [hec]
      rfl
    · intro i hi
      apply (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_tgt
    · refine ⟨?_, hres.2.2.2.2.2.2.2⟩
      have := hres.2.2.2.2.2.2.1
      dsimp only [ε]
      infer_instance

end CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The fixed small pro-etale site is essentially small in the coefficient universe.
Source: the size convention in the blueprint's pro-etale site
(blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
instance constantPeriodicSiteSmall (V : Scheme.{u}) :
    EssentiallySmall.{max r (u + 1)} V.ProEt := essentiallySmallSelf _

/-- Constant module sheafification after the canonical coefficient-universe lift.
The last functor generalizes the recorded constant module construction to the coefficient size,
then transports along the canonical isomorphism of ring sheafifications.
Source: Stacks Tags 03CY and 093J, and blueprint "The examples"
(blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
def constantPeriodicModuleFunctor (R : Type r) [CommRing R] (V : Scheme.{u}) :=
  ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} R ≃+* R).toRingHom ⋙
    ModuleCat.uliftFunctor.{u + 1, r} (ULift.{u + 1} R) ⋙
      siteConstantCommModuleFunctorSized (ProEt.topology V) (ULift.{u + 1} R)

/-- The constant multiplication-by-`t` endomorphism on the rank-one constant module.
Source: blueprint "The examples", periodic differential; Stacks Tag 093J
(blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
def constantPeriodicScalar (R : Type r) [CommRing R] (t : R) (V : Scheme.{u}) :=
  (constantPeriodicModuleFunctor R V).map (ModuleCat.ofHom (LinearMap.mulLeft R t))

/-- The constant quotient map to `R/(t)`, with its prescribed quotient scalar action.
Source: blueprint "The examples", augmentation; Stacks Tag 03CY
(blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
def constantPeriodicQuotientMap (R : Type r) [CommRing R] (t : R) (V : Scheme.{u}) :=
  (constantPeriodicModuleFunctor R V).map
    (ModuleCat.ofHom (Ideal.span ({t} : Set R)).mkQ)

/-- The actual constant-section map at the terminal pro-etale object `V`.
Source: Stacks Tag 03CY, sheafification unit, and blueprint "The examples"
(blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
def constantPeriodicSection (R : Type r) [CommRing R] (V : Scheme.{u})
    (M : ModuleCat.{r} R) (x : M) :=
  (siteConstantCommModuleUnitSized (ProEt.topology V) (ULift.{u + 1} R)
    ((ModuleCat.uliftFunctor.{u + 1, r} (ULift.{u + 1} R)).obj
      ((ModuleCat.restrictScalars
        (ULift.ringEquiv : ULift.{u + 1} R ≃+* R).toRingHom).obj M))).app
          (op (ProEt.mk (𝟙 V))) (ULift.up x)

set_option backward.isDefEq.respectTransparency false in
private instance periodicFunctor_limits (R : Type r) [CommRing R] (V : Scheme.{u}) :
    PreservesFiniteLimits (constantPeriodicModuleFunctor R V) := by
  unfold constantPeriodicModuleFunctor
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private instance periodicFunctor_colimits (R : Type r) [CommRing R] (V : Scheme.{u}) :
    PreservesFiniteColimits (constantPeriodicModuleFunctor R V) := by
  unfold constantPeriodicModuleFunctor
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private instance periodicFunctor_additive (R : Type r) [CommRing R] (V : Scheme.{u}) :
    (constantPeriodicModuleFunctor R V).Additive := by
  unfold constantPeriodicModuleFunctor
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private def periodicUnitIso (R : Type r) [CommRing R] (V : Scheme.{u}) :
    (constantPeriodicModuleFunctor R V).obj (ModuleCat.of R R) ≅
      SheafOfModules.unit ((sheafCompose (ProEt.topology V)
        (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
          ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
            (CommRingCat.of (ULift.{u + 1} R)))) := by
  exact sizedUnitIso (ProEt.topology V) (ULift.{u + 1} R)

set_option backward.isDefEq.respectTransparency false in
private theorem algebraic_periodic_exact (R : Type r) [CommRing R]
    (t : R) (ht : t ^ 2 = 0)
    (hann : ∀ a : R, t * a = 0 ↔ a ∈ Ideal.span ({t} : Set R)) :
    ∃ h : ModuleCat.ofHom (LinearMap.mulLeft R t) ≫
        ModuleCat.ofHom (LinearMap.mulLeft R t) = 0,
      (ShortComplex.mk _ _ h).Exact := by
  have h : ModuleCat.ofHom (LinearMap.mulLeft R t) ≫
      ModuleCat.ofHom (LinearMap.mulLeft R t) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change t * (t * a) = 0
    rw [← mul_assoc, ← pow_two, ht, zero_mul]
  refine ⟨h, (ShortComplex.moduleCat_exact_iff _).2 ?_⟩
  intro a ha
  change t * a = 0 at ha
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ((hann a).mp ha)
  exact ⟨b, hb.symm⟩

set_option backward.isDefEq.respectTransparency false in
private theorem algebraic_quotient_exact (R : Type r) [CommRing R] (t : R) :
    ∃ h : ModuleCat.ofHom (LinearMap.mulLeft R t) ≫
        ModuleCat.ofHom (Ideal.span ({t} : Set R)).mkQ = 0,
      (ShortComplex.mk _ _ h).Exact := by
  have h : ModuleCat.ofHom (LinearMap.mulLeft R t) ≫
      ModuleCat.ofHom (Ideal.span ({t} : Set R)).mkQ = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change (Submodule.Quotient.mk (t * a) : R ⧸ Ideal.span ({t} : Set R)) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact Ideal.mem_span_singleton.mpr ⟨a, rfl⟩
  refine ⟨h, (ShortComplex.moduleCat_exact_iff _).2 ?_⟩
  intro a ha
  change (Ideal.span ({t} : Set R)).mkQ a = 0 at ha
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ((Submodule.Quotient.mk_eq_zero _).mp ha)
  exact ⟨b, hb.symm⟩

set_option backward.isDefEq.respectTransparency false in
private theorem periodic_constants_injective (R : Type r) [CommRing R]
    (V : Scheme.{u}) (M : ModuleCat.{r} R) (hV : Nonempty V) :
    Function.Injective (constantPeriodicSection.{r, u} R V M) := by
  classical
  let J := ProEt.topology V
  let : EssentiallySmall.{max r (u + 1)} V.ProEt := constantPeriodicSiteSmall V
  let : HasSheafify J AddCommGrpCat.{max r (u + 1)} :=
    SheafOfModules.hasSheafify_coefficientUniverse
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max r (u + 1)} :=
    SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
  let U := ProEt.mk (𝟙 V)
  have hbot : (⊥ : Sieve U) ∉ J U := by
    intro h
    obtain ⟨Q, hQ, hQS⟩ := ProEt.mem_topology_iff.mp h
    obtain ⟨ι, W, f, rfl⟩ := Q.exists_eq_ofArrows
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hQ
    obtain ⟨i, y, hy⟩ :=
      ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1 hQ.2).1
        (Classical.choice hV)
    have hf := hQS _ _ (Presieve.ofArrows.mk i)
    simp at hf
  let N := ((ModuleCat.uliftFunctor.{u + 1, r} (ULift.{u + 1} R)).obj
    ((ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{u + 1} R ≃+* R).toRingHom).obj M))
  let P := ((siteConstantModulePresheafSized (C := V.ProEt) (ULift.{u + 1} R)).obj N)
  intro a b hab
  have hS := Presheaf.equalizerSieve_mem (D := AddCommGrpCat.{max r (u + 1)}) J
    (toSheafify J P.presheaf)
    (ULift.up.{u + 1, r} a) (ULift.up.{u + 1, r} b) hab
  by_contra hab'
  apply hbot
  convert hS using 1
  ext W g
  simp only [Sieve.bot_apply, Presheaf.equalizerSieve_apply, false_iff]
  change ¬ (ULift.up a : N) = ULift.up b
  simpa using hab'

set_option backward.isDefEq.respectTransparency false in
/-- The constant periodic complex is a termwise flat K-flat resolution, with the
canonical quotient as its cokernel and injective constants on any nonempty base.
Source: blueprint main-20261015, sec-proetale-coefficients,
sk-def-localizing-closure-ctf-equals-bc.proof.md, "The examples";
Stacks Tags 093J, 03CY and 06YQ
(blueprint: lem-sfb-constant-periodic-resolution-nonzero).

Proof:
1. Algebraically multiplication by t has image (t) and, by the annihilator hypothesis,
   kernel (t). The quotient map is surjective with kernel (t). Its cokernel is R/(t),
   t squared is zero, and t acts as zero on R/(t); this includes the zero ring.
2. Constant module presheaves preserve limits and colimits objectwise. Module
   sheafification preserves finite limits and colimits; transport along the canonical
   coefficient isomorphism preserves them too. Thus the sized constant module functor
   is exact. The sheafification universal property identifies its rank-one object
   with the unit module. Its maps give the stated multiplication and quotient maps.
3. Apply lem-sfb-exact-scalar-periodic-resolution to the constant ring sheaf and t.
   Its cokernel is canonically the constant quotient by step 2. This gives the
   augmented exact sequence, all term identifications and differentials, termwise
   flatness, and the K-flat augmentation. The cutoff is above degree zero.
4. If V is nonempty, local injectivity of the additive sheafification unit makes
   equal constant sections equal on a covering sieve. A pro-etale cover of a nonempty
   scheme has a nonempty member,
   where the constant-presheaf restriction is the identity, so the constants agree.
5. A nonzero element of R/(t) consequently has a nonzero constant section. A zero
   sheaf has only zero sections. No nonvanishing assertion is made for empty V. -/
theorem constant_periodic_resolution_nonzero (R : Type r) [CommRing R]
    (t : R) (ht : t ^ 2 = 0)
    (hann : ∀ a : R, t * a = 0 ↔ a ∈ Ideal.span ({t} : Set R)) (V : Scheme.{u}) :
    kernelSubobject (constantPeriodicScalar R t V) =
      imageSubobject (constantPeriodicScalar R t V) ∧
    (∃ e : cokernel (constantPeriodicScalar R t V) ≅
        (constantPeriodicModuleFunctor R V).obj
          (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R))),
      cokernel.π (constantPeriodicScalar R t V) ≫ e.hom =
        constantPeriodicQuotientMap R t V) ∧
    (∃ P : CochainComplex (SheafOfModules.{max r (u + 1)}
        ((sheafCompose (ProEt.topology V)
          (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
            ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R))))) ℤ,
      ∃ e : ∀ (i : ℤ), i ≤ 0 →
          (P.X i ≅ (constantPeriodicModuleFunctor R V).obj (ModuleCat.of R R)),
        (∀ (i : ℤ), 0 < i → IsZero (P.X i)) ∧
        (∀ (i : ℤ) (hi : i < 0) (hi' : i + 1 ≤ 0),
          P.d i (i + 1) ≫ (e (i + 1) hi').hom =
            (e i (le_of_lt hi)).hom ≫ constantPeriodicScalar R t V) ∧
        (∀ i : ℤ,
          SheafOfModules.IsFlatOnSite.{u + 1, u, max r (u + 1), max r (u + 1)}
            (J := ProEt.topology V)
            (R := (constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R))) (P.X i)) ∧
        (∃ ε : P ⟶ (HomologicalComplex.single _ (.up ℤ) 0).obj
            ((constantPeriodicModuleFunctor R V).obj
              (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)))),
          ε.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).hom =
            (e 0 (le_refl 0)).hom ≫ constantPeriodicQuotientMap R t V ∧
          (∀ i : ℤ, i ≠ 0 → ε.f i = 0) ∧
          CochainComplex.IsKFlatResolutionIndependentCoefficients.{u + 1, u, max r (u + 1)}
            (R := (constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R))) ε)) ∧
    (constantPeriodicModuleFunctor R V).map
      (t • 𝟙 (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)))) = 0 ∧
    (Nonempty V → Function.Injective
      (constantPeriodicSection R V (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R))))) ∧
    (Nontrivial (R ⧸ Ideal.span ({t} : Set R)) → Nonempty V →
      ¬ IsZero ((constantPeriodicModuleFunctor R V).obj
        (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R))))) := by
  classical
  let : EssentiallySmall.{max r (u + 1)} V.ProEt := constantPeriodicSiteSmall V
  let : HasSheafify (ProEt.topology V) AddCommGrpCat.{max r (u + 1)} :=
    SheafOfModules.hasSheafify_coefficientUniverse
  let : (ProEt.topology V).WEqualsLocallyBijective AddCommGrpCat.{max r (u + 1)} :=
    SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
  let F := constantPeriodicModuleFunctor R V
  let : F.PreservesHomology := inferInstance
  let μ : ModuleCat.of R R ⟶ ModuleCat.of R R :=
    ModuleCat.ofHom (LinearMap.mulLeft R t)
  let q : ModuleCat.of R R ⟶ ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)) :=
    ModuleCat.ofHom (Ideal.span ({t} : Set R)).mkQ
  obtain ⟨hμ, hμexact⟩ := algebraic_periodic_exact R t ht hann
  obtain ⟨hq, hqexact⟩ := algebraic_quotient_exact R t
  have hFμ : F.map μ ≫ F.map μ = 0 := by
    rw [← F.map_comp, hμ, F.map_zero]
  have hFexact : (ShortComplex.mk (F.map μ) (F.map μ) hFμ).Exact := hμexact.map F
  have hker : kernelSubobject (F.map μ) = imageSubobject (F.map μ) := by
    exact ((ShortComplex.exact_iff_image_eq_kernel _).mp hFexact).symm
  have : Epi q := (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)
  let : F.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_map_exact F (fun T hT ↦ hT.map F)
  have : Epi (F.map q) := Functor.map_epi F q
  have hFq : F.map μ ≫ F.map q = 0 := by
    rw [← F.map_comp, hq, F.map_zero]
  have hqmap : (ShortComplex.mk (F.map μ) (F.map q) hFq).Exact := hqexact.map F
  let e : cokernel (F.map μ) ≅ F.obj (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R))) :=
    (cokernelIsCokernel (F.map μ)).coconePointUniqueUpToIso hqmap.gIsCokernel
  have he : cokernel.π (F.map μ) ≫ e.hom = F.map q := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel (F.map μ)) hqmap.gIsCokernel WalkingParallelPair.one
  have hz : t • 𝟙 (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R))) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change t • a = 0
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change Ideal.Quotient.mk _ (t * a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr ⟨a, rfl⟩)
  have hinj := periodic_constants_injective R V
    (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)))
  refine ⟨hker, ⟨e, he⟩, ?_, ?_, hinj, ?_⟩
  · exact scalar_resolution_transport (ProEt.topology V)
      ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
        (CommRingCat.of (ULift.{u + 1} R))) _ _ (F.map μ) hFμ hFexact
      (periodicUnitIso R V) e (F.map q) he
  · change F.map _ = 0
    rw [hz, F.map_zero]
  · intro hR hV hzero
    let := hR
    let M := F.obj (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)))
    have hzobj := (SheafOfModules.evaluation _ (op (ProEt.mk (𝟙 V)))).map_isZero hzero
    have hsubs := ModuleCat.subsingleton_of_isZero hzobj
    have hsec : constantPeriodicSection R V (ModuleCat.of R
        (R ⧸ Ideal.span ({t} : Set R))) 0 = constantPeriodicSection R V
          (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R))) 1 := by
      apply @Subsingleton.elim _ hsubs
    have : (0 : R ⧸ Ideal.span ({t} : Set R)) = 1 := hinj hV hsec
    exact zero_ne_one this

end AlgebraicGeometry.Scheme
