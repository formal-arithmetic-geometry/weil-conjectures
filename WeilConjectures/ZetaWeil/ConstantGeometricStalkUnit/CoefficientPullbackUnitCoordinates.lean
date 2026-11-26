/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.IsomorphismDerivedPullback

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement

public import WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure
public import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparison
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import WeilConjectures.ZetaWeil.FiniteRegularCoefficientComparisons
public import WeilConjectures.ZetaWeil.FrobeniusPointTransport
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi

import all WeilConjectures.SmoothPurity.Point.PointSectionsScalarExtension
import all WeilConjectures.PoincareDuality.Canonical.CanonicalCoefficientPullbackReduction
import all WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure
import WeilConjectures.ZetaWeil.ConstantPullbackUnitQuasiIsomorphism.ConstantPullbackUnitQuasiIsomorphism

/-! # Finite and completed coefficient pullback units

This file constructs, for an arbitrary morphism of schemes `f : X ⟶ Y`, the finite coefficient
units for the pullback of the constant coefficient sheaves and the integral (completed) unit, and
proves that the integral unit is a quasi-isomorphism. These are used in the constant-sheaf case of
the Grothendieck–Lefschetz trace formula.

## Implementation details

These constructions are re-exported in `ConstantGeometricStalkUnit` for the geometric stalk
calculations. The strict integral unit is characterized by an existence and uniqueness statement
(`integralChainUnit_existsUnique`), so that no filler in a triangulated homotopy limit is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.ConstantGeometricStalkUnit

attribute [-instance] coefficientComplexModuleDerived pointScalarModuleDerived
  pointCompletedSheafDerived pointScalarAbLocallyBijective
  coefficientComplexIntegralLimits
  coefficientComplexIntegralColimits coefficientComplexRationalAdditive
  coefficientComplexRationalLimits coefficientComplexRationalColimits
  coefficientComplexFieldAdditive coefficientComplexFieldLimits coefficientComplexFieldColimits

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Multiplication on the finite coefficient unit, as the adjoint of the constant section one. -/
def finiteUnitHom {X Y : Scheme.{u}} (f : X ⟶ Y) (m : ℕ) :
    (sfIntrinsicPullback (Padic.coefficientExtensionRing l E (m + 1)) f).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E Y m)) ⟶
      SheafOfModules.unit (integralCoefficientSheaf l E X m) :=
  letI := Padic.finite_coefficientExtensionRing l E (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
  ((sfIntrinsicConstantModuleAdjunction f
    (Padic.coefficientExtensionRing l E (m + 1))).homEquiv _ _).symm
      ((SheafOfModules.unitHomEquiv _).symm
        (PresheafOfModules.sectionsMk (fun U ↦ (1 : (integralCoefficientSheaf l E X m).obj.obj
          ((proEtaleBaseChange f).op.obj U)))
          (fun {_ _} a ↦ map_one ((integralCoefficientSheaf l E X m).obj.map
            ((proEtaleBaseChange f).op.map a)).hom)))

/-- Transposing multiplication computes it on every adjunction generator. -/
private theorem finiteUnitHom_generator {X Y : Scheme.{u}} (f : X ⟶ Y) (m : ℕ)
    (V : Y.ProEt) (a : (integralCoefficientSheaf l E Y m).obj.obj (op V)) :
    letI := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
    (finiteUnitHom l E f m).val.app (op ((proEtaleBaseChange f).obj V))
      (((sfIntrinsicConstantModuleAdjunction f
        (Padic.coefficientExtensionRing l E (m + 1))).unit.app
          (SheafOfModules.unit (integralCoefficientSheaf l E Y m))).val.app (op V) a) =
      ((coefficientProEtaleDirectRingMap.{u, u} f
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))))).hom.app
          (op V)) a := by
  let := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
  let adj := sfIntrinsicConstantModuleAdjunction f
    (Padic.coefficientExtensionRing l E (m + 1))
  have h := (adj.homEquiv
    (SheafOfModules.unit (integralCoefficientSheaf l E Y m))
    (SheafOfModules.unit (integralCoefficientSheaf l E X m))).apply_symm_apply
    ((SheafOfModules.unitHomEquiv
      ((proEtaleConstantModuleDirectImage f
        (Padic.coefficientExtensionRing l E (m + 1))).obj
          (SheafOfModules.unit (integralCoefficientSheaf l E X m)))).symm
      (PresheafOfModules.sectionsMk (fun U ↦
        (1 : (integralCoefficientSheaf l E X m).obj.obj
          ((proEtaleBaseChange f).op.obj U)))
        (fun {_ _} b ↦ map_one ((integralCoefficientSheaf l E X m).obj.map
          ((proEtaleBaseChange f).op.map b)).hom)))
  rw [Adjunction.homEquiv_unit] at h
  have hv := congrArg (fun z ↦ z.val.app (op V) a) h
  let b : (integralCoefficientSheaf l E X m).obj.obj (op ((proEtaleBaseChange f).obj V)) :=
    ((coefficientProEtaleDirectRingMap.{u, u} f
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))))).hom.app
        (op V)) a
  change (finiteUnitHom l E f m).val.app (op ((proEtaleBaseChange f).obj V))
      ((adj.unit.app (SheafOfModules.unit (integralCoefficientSheaf l E Y m))).val.app
        (op V) a) =
    b * (1 : (integralCoefficientSheaf l E X m).obj.obj
      (op ((proEtaleBaseChange f).obj V))) at hv
  exact hv.trans (mul_one b)

private theorem finiteUnitHom_tensor {X Y : Scheme.{u}} (f : X ⟶ Y) (m : ℕ) :
    letI := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
    let A := CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))
    let φ : integralCoefficientSheaf l E Y m ⟶
        ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
          (ProEt.topology Y) (ProEt.topology X)).obj
            (integralCoefficientSheaf l E X m) :=
      ⟨Functor.whiskerRight (coefficientProEtaleDirectRingMap.{u, u} f A).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
    letI : (SheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint :=
      coefficientProEtaleModuleDirectImage_isRightAdjoint.{u, u} f A
    (inverseImageFiniteIntrinsicPullbackComparison f
      (Padic.coefficientExtensionRing l E (m + 1))).hom.app
        (SheafOfModules.unit (integralCoefficientSheaf l E Y m)) ≫
          finiteUnitHom l E f m = SheafOfModules.pullbackObjUnitToUnit φ := by
  let := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
  let A := CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))
  let φ : integralCoefficientSheaf l E Y m ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj
          (integralCoefficientSheaf l E X m) :=
    ⟨Functor.whiskerRight (coefficientProEtaleDirectRingMap.{u, u} f A).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let : (SheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint :=
    coefficientProEtaleModuleDirectImage_isRightAdjoint.{u, u} f A
  let adj₁ := coefficientProEtaleModuleAdjunction.{u, u} f A
  let adj₂ := sfIntrinsicConstantModuleAdjunction f
    (Padic.coefficientExtensionRing l E (m + 1))
  let e := adj₁.leftAdjointUniq adj₂
  change e.hom.app (SheafOfModules.unit (integralCoefficientSheaf l E Y m)) ≫
    finiteUnitHom l E f m = SheafOfModules.pullbackObjUnitToUnit φ
  apply (adj₁.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    adj₁.unit_leftAdjointUniq_hom_app adj₂]
  change adj₂.homEquiv _ _ (finiteUnitHom l E f m) = _
  rw [finiteUnitHom, Equiv.apply_symm_apply]
  change _ = (SheafOfModules.pullbackPushforwardAdjunction φ).homEquiv _ _
    (SheafOfModules.pullbackObjUnitToUnit φ)
  rw [SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  apply (SheafOfModules.unitHomEquiv _).injective
  simp only [Equiv.apply_symm_apply]
  ext U
  simp only [SheafOfModules.unitHomEquiv_apply_coe]
  change (1 : (integralCoefficientSheaf l E X m).obj.obj
    ((proEtaleBaseChange f).op.obj U)) = φ.hom.app U 1
  exact (map_one _).symm

/-- The finite multiplication is invertible, including the first positive quotient. -/
theorem finiteUnitHom_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (m : ℕ) :
    IsIso (finiteUnitHom l E f m) := by
  let := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
  let A := CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))
  let φ : integralCoefficientSheaf l E Y m ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj
          (integralCoefficientSheaf l E X m) :=
    ⟨Functor.whiskerRight (coefficientProEtaleDirectRingMap.{u, u} f A).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let : (SheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint :=
    coefficientProEtaleModuleDirectImage_isRightAdjoint.{u, u} f A
  let adj₁ := coefficientProEtaleModuleAdjunction.{u, u} f A
  let adj₂ := sfIntrinsicConstantModuleAdjunction f
    (Padic.coefficientExtensionRing l E (m + 1))
  let e := adj₁.leftAdjointUniq adj₂
  have he : e.hom.app (SheafOfModules.unit (integralCoefficientSheaf l E Y m)) ≫
      finiteUnitHom l E f m = SheafOfModules.pullbackObjUnitToUnit φ :=
    finiteUnitHom_tensor l E f m
  have : IsIso (e.hom.app (SheafOfModules.unit (integralCoefficientSheaf l E Y m)) ≫
      finiteUnitHom l E f m) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (e.hom.app (SheafOfModules.unit (integralCoefficientSheaf l E Y m)))
    (finiteUnitHom l E f m)

/-- The finite derived unit comparison, with its exact single-complex comparison. -/
def finiteUnit {X Y : Scheme.{u}} (f : X ⟶ Y) (m : ℕ) :
    (finiteDerivedPullback l E m f).obj (finiteConstantCoefficientObject l E Y m) ≅
      finiteConstantCoefficientObject l E X m :=
  letI := Padic.finite_coefficientExtensionRing l E (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
  ((sfIntrinsicPullback
    (Padic.coefficientExtensionRing l E (m + 1)) f).mapDerivedCategorySingleFunctor
      0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (@asIso _ _ _ _ (finiteUnitHom l E f m) (finiteUnitHom_isIso l E f m))

section
attribute [local irreducible] unrestrictedIntegralReductionExistence limit
  chainUnitCandidate pullbackUnitProduct pullbackUnitLevel

/-- There is a unique normalized strict unit chain map for an arbitrary morphism of schemes,
extending the construction used for the Weil automorphism. -/
theorem integralChainUnit_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! η : constantWeilIntegralComplex l E X ⟶
        (integralOperationsPullbackComplexFunctor l E f).obj
          (constantWeilIntegralComplex l E Y),
      (∀ (m : ℕ) (V : Y.ProEt),
        ((η.f 0 ≫
          (CochainComplex.mappingCocone.fst
            (constantWeilPullbackRoosEndomorphism l E f)).f 0 ≫
          (Pi.π (fun j ↦ (constantWeilPullbackTower l E f).obj (op j)) m).f 0).val.app
            (op ((proEtaleBaseChange f).obj V)))
          (constantWeilUnitSection l E X ((proEtaleBaseChange f).obj V)) =
        integralOperationsPullbackGenerator l E f m
          (((unrestrictedIntegralFiniteComplex l E Y m).obj
            (constantWeilIntegralComplex l E Y)).X 0) V
          (constantWeilReducedUnitSection l E Y m V)) ∧
      (∀ i : ℤ, η.f i ≫
        (CochainComplex.mappingCocone.snd
          (constantWeilPullbackRoosEndomorphism l E f)).v i (i - 1) (by omega) = 0) := by
  refine ⟨chainUnitCandidate l E f, ⟨?_, ?_⟩, ?_⟩
  · intro m V
    exact chainUnitCandidate_generators l E f m V
  · intro i
    simp only [chainUnitCandidate, CochainComplex.mappingCocone.lift_f_snd_v,
      CochainComplex.HomComplex.Cochain.zero_v]
  · intro η hη
    exact normalized_chainUnit_unique l E f η hη

end

/-- The uniquely specified strict chain map, with real cochain data. -/
def integralChainUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (integralChainUnit_existsUnique l E f).exists.choose

/-- The strict coefficient unit is a quasi-isomorphism for arbitrary pullback. -/
theorem integralChainUnit_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (DerivedCategory.Q.map (integralChainUnit l E f)) := by
  exact ConstantPullbackUnitQuasiIsomorphism.normalizedChainUnit_isIso l E f
    (integralChainUnit l E f) (integralChainUnit_existsUnique l E f).exists.choose_spec

/-- The integral unit identification, using the inverse normalized strict-cone map. -/
def integralUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (integralDerivedPullback l E f).obj (integralConstantCoefficientObject l E Y) ≅
      integralConstantCoefficientObject l E X :=
  (integralDerivedPullbackComparison l E f).app (constantWeilIntegralGood l E Y) ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map (integralChainUnit l E f))
      (integralChainUnit_isIso l E f)).symm

section
attribute [local irreducible] coefficientFinitePullIso canonicalCoefficientFiniteKappaComplex
  canonicalCoefficientFiniteUnit constantSheaf unrestrictedIntegralReductionExistence limit

end

/-- For an isomorphism `g`, the generalized strict unit agrees with the canonical integral Weil
map. -/
theorem integralUnit_canonicalWeil {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    integralUnit l E g = constantWeilIntegralTheta l E g := by
  simp only [constantWeilIntegralTheta, constantWeilIntegralLambda, Iso.trans_assoc,
    Iso.symm_self_id, Iso.trans_refl]
  rfl

end WeilConjectures.ConstantGeometricStalkUnit
