/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.ContinuousRationalDerivedRealization
public import Sheaf.Paper.RationalDirectImageRealization
public import Sheaf.Paper.AdicHeartIntrinsicFibres
public import Sheaf.Paper.FieldStageOrdinaryRealization
public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
public import Sheaf.Paper.CompletedExtensionZeroComparison

/-! # Canonical point and ordinary-image section models

Source: Bhatt--Scholze 6.8.14--6.8.15; Milne 18.1, 18.3(b)
(blueprint: def-a1-adic-section-canonical-models).

## Main definitions

- `PointSection`: point-fibre H0/Hom, fixed by evaluation on 1 ⊗ 1.
- `IntegralPushModel`, `ImageModel`: representative and Roos projection normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w uC vC uD vD wC wD
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

namespace AdicCompactificationSections

open scoped ChangeOfRings

/-- The actual unit of ordinary coefficient tensor extension, x ↦ 1 ⊗ x.
Source: BS 6.8.2(1)
(blueprint: def-a1-adic-section-canonical-models). -/
def scalarUnit {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (ι : A →+* B) {M : ModuleCat.{w} A} (x : M) :
    (ModuleCat.extendScalars ι).obj M := (1 : B) ⊗ₜ[A, ι] x

/-- Reuse the separated finite-type geometry of the adic fibre dependency.
Source: BS 6.8.14--6.8.15
(blueprint: def-a1-adic-section-canonical-models). -/
abbrev Geometry (D : FiniteFieldDatum.{u}) := PerAdic.Base D.k

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

/-- The continuous-realization hypotheses follow from the recorded finite-type geometry.
Source: BS 6.8.14 and lem-per-adic-heart-pullback-fibres
(blueprint: def-a1-adic-section-canonical-models). -/
def realizationBase (W : Geometry D) : ContinuousRational.Base l :=
  letI : Fact (IsUnit (l : D.k)) := ⟨finiteFieldDatumPrimeUnit D l hl⟩
  { scheme := W.scheme
    noetherian := PerAdic.baseNoetherian W
    dimension := (PerAdic.base_properties l W).2.1
    prime_unit := (PerAdic.base_properties l W).2.2 }

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Global continuous sections, with the constant-section E-action. Evaluation is
Mathlib's module evaluation at the terminal pro-etale object, followed by scalar restriction.
Source: BS 6.8.1; Milne 18.1
(blueprint: def-a1-adic-section-canonical-models). -/
def sections (W : Scheme.{u}) :
    pbcModules W (rationalCoefficientSheaf l W E) ⥤ ModuleCat.{u + 1} E :=
  SheafOfModules.forget _ ⋙
    PresheafOfModules.evaluation _ (Opposite.op (ProEt.mk (𝟙 W))) ⋙
      ModuleCat.restrictScalars
        { toFun := fun a ↦ (ContinuousRational.scalarSections l E W a).val
            (Opposite.op (ProEt.mk (𝟙 W)))
          map_one' := rfl
          map_mul' := fun _ _ ↦ rfl
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }

/-- The coefficient object at the geometric base point, with its existing raw presentation.
Source: BS 6.8.14(2), point normalization
(blueprint: def-a1-adic-section-canonical-models). -/
def pointCoefficient := rationalCohomologyCoefficient D l hl E (Spec (.of D.k))

/-- The actual coefficient-unit complex after point sections and rationalization.
Both comparisons are the exact-functor single-complex comparisons.
Source: BS 6.8.14(2), point normalization
(blueprint: def-a1-adic-section-canonical-models). -/
def pointCoefficientSectionsIso :
    (pointModuleDerivedRationalization l E).obj
        ((pointCompletedDerivedSections D.k l E).obj
          (pointCoefficient D l hl E).obj.obj) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((pointModuleRationalization l E).obj
          ((pointCompletedSections D.k l E).obj
            (SheafOfModules.unit
              (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k)))))) :=
  (pointModuleDerivedRationalization l E).mapIso
      ((pointCompletedSections D.k l E).mapDerivedCategorySingleFunctor 0 |>.app
        (SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k))))) ≪≫
    ((pointModuleRationalization l E).mapDerivedCategorySingleFunctor 0).app _

/-- Canonical coefficient-unit contraction, specified on tensor generators.
The integral transport is fixed by 1 ↦ 1 and the tensor comparison by multiplication.
Source: BS 6.8.14(2), 6.8.15
(blueprint: def-a1-adic-section-canonical-models). -/
structure CoefficientUnitModel (W : Scheme.{u})
    (φ : pbcAdicCompletion W (pbcIntegralDatum l E) ⟶ rationalCoefficientSheaf l W E) where
  integral : ((SheafOfModules.restrictScalars.{u + 1}
    (integralDetailedCoefficientComparison W l E).hom).obj
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W))) ≅
    SheafOfModules.unit (proEtaleModuleCoefficients (pbcAdicCompletion W (pbcIntegralDatum l E)))
  integral_one : ∀ V : W.ProEtᵒᵖ, integral.hom.val.app V
      (1 : (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj V) =
    (1 : (proEtaleModuleCoefficients (pbcAdicCompletion W (pbcIntegralDatum l E))).obj.obj V)
  tensor : (pbcExtend φ).obj
      (SheafOfModules.unit
        (proEtaleModuleCoefficients (pbcAdicCompletion W (pbcIntegralDatum l E)))) ≅
    SheafOfModules.unit (proEtaleModuleCoefficients (rationalCoefficientSheaf l W E))
  tensor_sections : ∀ (V : W.ProEtᵒᵖ)
      (a : (rationalCoefficientSheaf l W E).obj.obj V)
      (b : (pbcAdicCompletion W (pbcIntegralDatum l E)).obj.obj V),
    tensor.hom.val.app V (pbcTensorSection φ _ V a b) = a * φ.hom.app V b

/-- The recorded inverse coefficient transport on ordinary module sheaves.
Source: Stacks 099N (blueprint: def-a1-adic-section-canonical-models). -/
abbrev completedModel (W : Scheme.{u}) :=
  SheafOfModules.restrictScalars.{u + 1}
    (integralDetailedCoefficientComparison W l E).hom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- The coefficient transport is the existing additive scalar restriction.
Source: Stacks 099N (blueprint: def-a1-adic-section-canonical-models). -/
instance completedModel_additive (W : Scheme.{u}) :
    (completedModel l E W).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars.{u + 1}
    (integralDetailedCoefficientComparison W l E).hom).Additive

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Reuse zero preservation of the actual additive coefficient transport.
Source: Stacks 099N (blueprint: def-a1-adic-section-canonical-models). -/
instance completedModel_zero (W : Scheme.{u}) :
    (completedModel l E W).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive (completedModel l E W)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Cache zero preservation for the literal ordinary push/transport composite.
Source: Stacks 099N (blueprint: def-a1-adic-section-canonical-models). -/
instance completedPushModel_zero {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sfCompletedModuleDirectImage l E f ⋙ completedModel l E Y).PreservesZeroMorphisms :=
  letI := sfCompletedModuleDirectImage_additive l E f
  letI := completedModel_additive l E Y
  Functor.preservesZeroMorphisms_comp _ _

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Cache zero preservation for coefficient transport followed by actual pushforward.
Source: Stacks 099N (blueprint: def-a1-adic-section-canonical-models). -/
instance modelActualPush_zero {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (completedModel l E X ⋙ pbcActualModulePush f
      (pbcIntegralDatum l E)).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_comp _ _

/-- The existing exact coefficient restriction preserves finite limits.
Source: Stacks 099N (blueprint: def-a1-adic-section-canonical-models). -/
instance completedModel_limits (W : Scheme.{u}) :
    PreservesFiniteLimits (completedModel l E W) :=
  (integralDetailedCoefficientRestriction_exact W l E).1

/-- The existing exact coefficient restriction preserves finite colimits.
Source: Stacks 099N (blueprint: def-a1-adic-section-canonical-models). -/
instance completedModel_colimits (W : Scheme.{u}) :
    PreservesFiniteColimits (completedModel l E W) :=
  (integralDetailedCoefficientRestriction_exact W l E).2

/-- Realize the actual integral coefficient unit and contract its derived tensor.
Only the specified exact coefficient transport and the universal tensor counit occur.
Source: BS 6.8.14(2) (blueprint: def-a1-adic-section-canonical-models). -/
def coefficientUnitArrow (W : Scheme.{u})
    (φ : pbcAdicCompletion W (pbcIntegralDatum l E) ⟶ rationalCoefficientSheaf l W E)
    (M : CoefficientUnitModel l E W φ) :
    (pbcDerivedExtend φ).obj ((integralDetailedTransport W l E).obj
      (integralCohomologyCoefficient D l hl E W).obj) ⟶
      (DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (proEtaleModuleCoefficients (rationalCoefficientSheaf l W E))) :=
  (pbcDerivedExtend φ).map
      (((SheafOfModules.restrictScalars.{u + 1}
        (integralDetailedCoefficientComparison W l E).hom).mapDerivedCategorySingleFunctor
          0).hom.app _ ≫ (DerivedCategory.singleFunctor _ 0).map M.integral.hom) ≫
    pbcComplexCounit φ ((CochainComplex.singleFunctor _ 0).obj
      (SheafOfModules.unit
        (proEtaleModuleCoefficients (pbcAdicCompletion W (pbcIntegralDatum l E))))) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex (pbcExtend φ) (.up ℤ) 0).hom.app _) ≫
    (DerivedCategory.singleFunctor _ 0).map M.tensor.hom

/-- Exact-functor cohomology comparison with independent localization universes.
This is the universal localization lift of the termwise homology comparison.
Source: Stacks 05RU (blueprint: def-a1-adic-section-canonical-models). -/
def homologyTransport {C : Type uC} {C' : Type uD}
    [Category.{vC} C] [Category.{vD} C'] [Abelian C] [Abelian C']
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} C']
    (F : C ⥤ C') [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n : ℤ) : DerivedCategory.homologyFunctor C n ⋙ F ≅
      F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C' n :=
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n ⋙ F)
      (DerivedCategory.homologyFunctor C n ⋙ F) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C n) F⟩
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n ⋙ F)
      (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C' n) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactors (DerivedCategory.homologyFunctor C' n) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactors C' n) ≪≫
      F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n⟩
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n ⋙ F)
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n ⋙ F)
    (DerivedCategory.homologyFunctor C n ⋙ F)
    (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C' n) (Iso.refl _)

/-- A normalized point-fibre H0-to-Hom map. Its unit class is fixed by the actual
pointRationalNormalization and the tensor 1 ⊗ 1, and its Hom map by evaluation on
that class. Thus neither map can be rescaled independently.
Source: BS 6.8.14(2); Milne 18.1
(blueprint: def-a1-adic-section-canonical-models). -/
structure PointSection (R : ContinuousRational.Family.{u} l) where
  J : sfRationalConstructibleCategory l E (Spec (.of D.k)) ⥤
    DerivedCategory (pbcModules (Spec (.of D.k))
      (rationalCoefficientSheaf l (Spec (.of D.k)) E))
  integral : sfRationalConstructibleLocalization l E (Spec (.of D.k)) ⋙ J ≅
    (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙
      integralDetailedTransport (Spec (.of D.k)) l E ⋙
      pbcDerivedExtend
        ((R.realization E (realizationBase D l hl
          ⟨Spec (.of D.k)⟩)).integralIso.hom ≫
          (R.realization E (realizationBase D l hl ⟨Spec (.of D.k)⟩)).inclusion)
  faithfully : ∀ K M, Function.Bijective (J.map : (K ⟶ M) → (J.obj K ⟶ J.obj M))
  one : (DerivedCategory.coefficientFdCohomology E 0).obj
    ((pointRationalFibre D l hl E).obj (pointCoefficient D l hl E))
  one_normalized :
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u + 1} E) 0).hom.app _)
      ((DerivedCategory.homologyFunctor _ 0).map
        ((pointRationalNormalization D l hl E (pointCoefficient D l hl E)).hom ≫
          (pointCoefficientSectionsIso D l hl E).hom)
        ((@homologyTransport.{u + 1, u, u + 2, u + 1, u, u + 2}
          (ModuleCat.{u} E) (ModuleCat.{u + 1} E) _ _ _ _
          (HasDerivedCategory.ofHasKInjectiveResolutions.{u} _) _
          (ModuleCat.uliftFunctor.{u + 1, u} E) _ _ _ 0).hom.app
          ((pointRationalFibre D l hl E).obj (pointCoefficient D l hl E)).obj
            (ULift.up (by
              simpa [DerivedCategory.coefficientFdCohomology] using one)))) =
      scalarUnit (M := (pointCompletedSections D.k l E).obj
        (SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k)))))
        (algebraMap (Padic.coefficientExtensionIntegers l E) E)
        (1 : (completedIntegralCoefficientSheafUnrestricted l E
          (Spec (.of D.k))).obj.obj (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k))))))
  hom : ∀ K : sfRationalConstructibleCategory l E (Spec (.of D.k)),
    ((DerivedCategory.coefficientFdCohomology E 0).obj
      ((pointRationalFibre D l hl E).obj K) : Type u) ≃ₗ[E]
        (pointCoefficient D l hl E ⟶ K)
  evaluation : ∀ K x,
    (DerivedCategory.coefficientFdCohomology E 0).map
      ((pointRationalFibre D l hl E).map (hom K x)) one = x
  unit : J.obj (pointCoefficient D l hl E) ≅
    (DerivedCategory.singleFunctor _ 0).obj
      (SheafOfModules.unit (proEtaleModuleCoefficients
        (rationalCoefficientSheaf l (Spec (.of D.k)) E)))
  unit_model : CoefficientUnitModel l E (Spec (.of D.k))
    ((R.realization E (realizationBase D l hl ⟨Spec (.of D.k)⟩)).integralIso.hom ≫
      (R.realization E (realizationBase D l hl ⟨Spec (.of D.k)⟩)).inclusion)
  unit_normalized : unit.hom =
    integral.hom.app (integralCohomologyCoefficient D l hl E (Spec (.of D.k))) ≫
      coefficientUnitArrow D l hl E (Spec (.of D.k))
        ((R.realization E (realizationBase D l hl ⟨Spec (.of D.k)⟩)).integralIso.hom ≫
          (R.realization E (realizationBase D l hl ⟨Spec (.of D.k)⟩)).inclusion) unit_model

/-- The universal right-derived unit at a complex, with the quotient comparison inserted.
Source: Stacks 07A5 (blueprint: def-a1-adic-section-canonical-models). -/
def representativePushUnit {C : Type uC} {C' : Type uD} [Category.{vC} C] [Category.{vD} C']
    [Abelian C] [Abelian C'] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} C']
    [Abelian.HasKInjectiveResolutions C] (G : C ⥤ C') [G.Additive]
    (P : CochainComplex C ℤ) :
    DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj P) ⟶
      G.rightDerivedFunctor.obj (DerivedCategory.Q.obj P) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj P) ≫
      G.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app P)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Identity-on-sections transport of ordinary completed direct image and its
universal right-derived comparison. The representative equation fixes the latter
through actual right-derived units, on every complex.
Source: Stacks 03DA, 07A5, 099N
(blueprint: def-a1-adic-section-canonical-models). -/
structure IntegralPushModel {X Y : Scheme.{u}} (f : X ⟶ Y) where
  ordinary : sfCompletedModuleDirectImage l E f ⋙ completedModel l E Y ≅
    completedModel l E X ⋙ pbcActualModulePush f (pbcIntegralDatum l E)
  ordinary_sections : ∀ (M : integralTowerModules l E X) (V : Y.ProEtᵒᵖ)
      (x : M.val.obj ((proEtaleBaseChange f).op.obj V)),
    (ordinary.hom.app M).val.app V x = x
  derived : sfCompletedDerivedDirectImage l E f ⋙ integralDetailedTransport Y l E ≅
    integralDetailedTransport X l E ⋙ pbcActualDerivedPush f (pbcIntegralDatum l E)
  representative : ∀ P : CochainComplex (integralTowerModules l E X) ℤ,
    (integralDetailedTransport Y l E).map
        (representativePushUnit (sfCompletedModuleDirectImage l E f) P) ≫
      derived.hom.app (DerivedCategory.Q.obj P) =
    (completedModel l E Y).mapDerivedCategoryFactors.hom.app
        (((sfCompletedModuleDirectImage l E f).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P) ≫
      representativePushUnit (pbcActualModulePush f (pbcIntegralDatum l E))
        (((completedModel l E X).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (pbcActualDerivedPush f (pbcIntegralDatum l E)).map
        ((completedModel l E X).mapDerivedCategoryFactors.inv.app P)

/-- The actual positive finite coefficient ring is finite.
Source: BS 6.8.2 (blueprint: def-a1-adic-section-canonical-models). -/
instance positiveCoefficientFinite (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

set_option backward.isDefEq.respectTransparency.types false
/-- The finite identity image, fixed by diagonal restriction on ordinary sections
and by the actual right-derived unit on every complex.
Source: Stacks 07A5, 0D6D (blueprint: def-a1-adic-section-canonical-models). -/
structure FiniteIdentityImage (W : Scheme.{u}) (n : ℕ) where
  ordinary : proEtaleConstantModuleDirectImage (𝟙 W)
    (Padic.coefficientExtensionRing l E (n + 1)) ≅ 𝟭 _
  sections : ∀ (M : proEtaleRingModules W
      (proEtaleConstantRing W (Padic.coefficientExtensionRing l E (n + 1))))
      (V : W.ProEt)
      (x : M.val.obj (Opposite.op ((proEtaleBaseChange (𝟙 W)).obj V))),
    (ordinary.hom.app M).val.app (Opposite.op V) x =
      M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ W).inv.app V).op x
  derived : proEtaleConstantDerivedDirectImage (𝟙 W)
    (Padic.coefficientExtensionRing l E (n + 1)) ≅ 𝟭 _
  representative : ∀ P : CochainComplex (proEtaleRingModules W
      (proEtaleConstantRing W (Padic.coefficientExtensionRing l E (n + 1)))) ℤ,
    representativePushUnit (proEtaleConstantModuleDirectImage (𝟙 W)
        (Padic.coefficientExtensionRing l E (n + 1))) P ≫
      derived.hom.app (DerivedCategory.Q.obj P) =
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)

/-- Recover precisely the product used in ordinary cohomology's Roos choice.
Source: BS 6.7.2 (blueprint: def-a1-adic-section-canonical-models). -/
abbrev imageProduct (W : Geometry D) (K : sfIntegralConstructibleCategory l E W.scheme) :
    HasProduct (sfDirectImageTerm l E (W.scheme ↘ Spec (.of D.k)) K.obj) :=
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (W.scheme ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := inferInstance
  (sfIntegralDirectImage_constructible D.k l (finiteFieldDatumPrimeUnit D l hl)
    E (W.scheme ↘ Spec (.of D.k)) K.obj K.property).1.choose

/-- Recover precisely the Roos image and projection used by integralImage.
Source: BS 6.7.2 (blueprint: def-a1-adic-section-canonical-models). -/
def chosenImage (W : Geometry D) (K : sfIntegralConstructibleCategory l E W.scheme) :
    letI := imageProduct D l hl E W K
    SfIntegralDirectImage l E (W.scheme ↘ Spec (.of D.k)) K.obj :=
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (W.scheme ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := inferInstance
  letI := imageProduct D l hl E W K
  (sfIntegralDirectImage_constructible D.k l (finiteFieldDatumPrimeUnit D l hl)
    E (W.scheme ↘ Spec (.of D.k)) K.obj K.property).1.choose_spec.some

/-- The ordinary-cohomology object and the recovered Roos vertex are definitionally
identical; expose this identity once for the comparison diagrams.
Source: BS 6.7.2 (blueprint: def-a1-adic-section-canonical-models). -/
def imageObjectIso (W : Geometry D) (K : sfIntegralConstructibleCategory l E W.scheme) :
    (integralImage D l hl E W.scheme K).obj ≅ (chosenImage D l hl E W K).obj :=
  Iso.refl _

/-- Equality of the actual finite Roos projections with scalar-reduction adjuncts.
Source: BS 6.7.2; Stacks 0A07
(blueprint: def-a1-adic-section-canonical-models). -/
def ImageProjectionNormalized (W : Geometry D)
    (K : sfIntegralConstructibleCategory l E W.scheme)
    (roos : (chosenImage D l hl E W K).obj ≅
      (sfCompletedDerivedDirectImage l E (W.scheme ↘ Spec (.of D.k))).obj K.obj) : Prop :=
  letI := imageProduct D l hl E W K
  ∀ n : ℕ,
    roos.inv ≫ (chosenImage D l hl E W K).projection ≫
        Pi.π (sfDirectImageTerm l E (W.scheme ↘ Spec (.of D.k)) K.obj) n =
      (sfCompletedDerivedDirectImage l E (W.scheme ↘ Spec (.of D.k))).map
        ((derivedScalarExtensionRestrictionAdjunction l E W.scheme n).choose.unit.app K.obj) ≫
        (sfDerivedRestrictionComparison l E (W.scheme ↘ Spec (.of D.k)) n).hom.app
          ((scalarReductionDerivedExtension l E W.scheme n).obj K.obj)

/-- The integral image comparison retains the actual Roos projections. The product
and subtype store precisely the transport, isomorphism and projection equation.
Source: BS 6.7.2; Stacks 0A07
(blueprint: def-a1-adic-section-canonical-models). -/
def ImageModel (W : Geometry D) (K : sfIntegralConstructibleCategory l E W.scheme) :=
  IntegralPushModel l E (W.scheme ↘ Spec (.of D.k)) ×
    { roos : (chosenImage D l hl E W K).obj ≅
        (sfCompletedDerivedDirectImage l E (W.scheme ↘ Spec (.of D.k))).obj K.obj //
      ImageProjectionNormalized D l hl E W K roos }

/-- The specified transport to the actual completed pushforward.
Source: BS 6.7.2; Stacks 099N (blueprint: def-a1-adic-section-canonical-models). -/
def ImageModel.transport {W : Geometry D} {K : sfIntegralConstructibleCategory l E W.scheme}
    (M : ImageModel D l hl E W K) : IntegralPushModel l E (W.scheme ↘ Spec (.of D.k)) := M.1

/-- The normalized isomorphism from the chosen Roos vertex.
Source: BS 6.7.2 (blueprint: def-a1-adic-section-canonical-models). -/
def ImageModel.roos {W : Geometry D} {K : sfIntegralConstructibleCategory l E W.scheme}
    (M : ImageModel D l hl E W K) :
    (chosenImage D l hl E W K).obj ≅
      (sfCompletedDerivedDirectImage l E (W.scheme ↘ Spec (.of D.k))).obj K.obj := M.2.val

/-- Retain the actual projection equation stored in the subtype.
Source: BS 6.7.2; Stacks 0A07 (blueprint: def-a1-adic-section-canonical-models). -/
abbrev ImageModel.projections {W : Geometry D}
    {K : sfIntegralConstructibleCategory l E W.scheme} (M : ImageModel D l hl E W K) :
    ImageProjectionNormalized D l hl E W K M.roos := M.2.property

end AdicCompactificationSections
end WeilConjectures
