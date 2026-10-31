/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.IsomorphismDerivedPullback
public import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.CoefficientPullbackUnitCoordinates
public import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.ConstantGeometricStalkData

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
public import WeilConjectures.SixFunctors.Frobenius.FrobeniusPointTransport
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi

import all WeilConjectures.SmoothPurity.Point.PointSectionsScalarExtension
import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology
import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.FinitePullbackUnitComposition
import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.FinitePointTransportUnit
import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.IntegralPullbackUnitComposition
import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.PointTransportIntegralScalar
import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.ReturnWeilIntegralScalar
import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.IntegralPointTransportUnit
import all WeilConjectures.SixFunctors.Frobenius.FrobeniusPointTransportNatural

/-! # Constant geometric stalks and the coefficient unit

Source: main-20261015, sec-zeta-weil/sk-thm-tracetodeterminant,
prop-every-iterate-trace.proof.md, constant-sheaf clause, reviewed expansion step 5
(blueprint: lem-zl-constant-geometric-stalk-unit).

All finite indices denote exponent m+1. The integral coefficient is the completed
ring sheaf. The maps below retain the actual adjunction units and strict Roos model.

## Main statements

* `embeddingPoint_return`: the semilinear return for every allowed embedding.
* `finiteStalkUnit`, `integralStalkUnit`, `rationalStalkUnit`: coefficient-unit coordinates.
* `finiteOperator_unit`, `integralOperator_unit`, `rationalOperator_unit`: identity operators.
* `finiteUnit_reduction`, `integralUnit_projection`, `section_reductions`: actual quotient squares.
* `rationalStalkUnit_existsUnique`, `rationalOperator_scalar`: rationalization squares.
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
  pointCompletedSheafDerived pointScalarAbSheafify pointScalarAbLocallyBijective
  coefficientComplexIntegralAdditive coefficientComplexIntegralLimits
  coefficientComplexIntegralColimits coefficientComplexRationalAdditive
  coefficientComplexRationalLimits coefficientComplexRationalColimits
  coefficientComplexFieldAdditive coefficientComplexFieldLimits coefficientComplexFieldColimits

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- The coefficient-to-section map at the finite point, preserving every constant a.
Source: reviewed expansion step 2 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def finiteSection (m : ℕ) :
    ModuleCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) ⟶
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E (Spec (.of D.k)) m)) :=
  ModuleCat.ofHom
    (Y := (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).obj
      (SheafOfModules.unit (integralCoefficientSheaf l E (Spec (.of D.k)) m)))
    { toFun := pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (m + 1))
      map_add' := map_add _
      map_smul' := fun a b ↦ by
        change _ = (pointConstantSectionMap D.k
          (Padic.coefficientExtensionRing l E (m + 1)) a) *
            (pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (m + 1)) b)
        exact map_mul _ a b }

/-- The coefficient-to-section map for completed integral scalars.
Source: reviewed expansion step 6 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralSection :
    ModuleCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
      (pointIntegralSections l E D.k).obj
        (SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k)))) :=
  ModuleCat.ofHom
    (Y := (pointIntegralSections l E D.k).obj
      (SheafOfModules.unit
        (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k)))))
    { toFun := pointIntegralSectionMap l E D.k
      map_add' := map_add _
      map_smul' := fun a b ↦ by
        change _ = pointIntegralSectionMap l E D.k a * pointIntegralSectionMap l E D.k b
        exact map_mul _ a b }

/-- Both section maps are invertible with the canonical coefficient actions.
Source: reviewed expansion steps 2 and 6 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: Spec k has one point. Finite constant sections are the coefficient ring by
constant functions and evaluation. Limits of sheaves are sectionwise, so completed
sections are lim A_m. Completeness of the coefficient DVR identifies this limit with
O_E via its actual quotient maps; uniqueness follows from separatedness. -/
theorem section_isIso :
    (∀ m : ℕ, IsIso (finiteSection l E D m)) ∧ IsIso (integralSection l E D) := by
  constructor
  · intro m
    apply (ConcreteCategory.isIso_iff_bijective _).2
    exact AlgebraicGeometry.ProEtale.bijective_toSheafify_app_of_iso (Iso.refl _)
      ((Functor.const (Scheme.ProEt (Spec (.of D.k)))ᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))))
  · apply (ConcreteCategory.isIso_iff_bijective _).2
    change Function.Bijective (pointIntegralSectionMap l E D.k)
    have h := pointCompletedConstant_bijective D.k l E
    exact h.comp (ULift.ringEquiv : ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l E) ≃+*
        Padic.coefficientExtensionIntegers l E).bijective

/-- Finite sections identified with the regular coefficient module in degree zero.
Source: reviewed expansion step 2 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def finiteSectionsUnit (m : ℕ) :
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.obj
        (finiteConstantCoefficientObject l E (Spec (.of D.k)) m) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (ModuleCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))) :=
  ((pointFiniteSections D.k
    (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategorySingleFunctor
    0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (@asIso _ _ _ _ (finiteSection l E D m) ((section_isIso l E D).1 m)).symm

/-- Completed integral sections in coefficient-unit coordinates.
Source: reviewed expansion step 6 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralSectionsUnit :
    (pointFibreIntegralAmbient D l E).obj (integralConstantCoefficientObject l E (Spec (.of D.k))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (ModuleCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) :=
  ((pointIntegralSections l E D.k).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (@asIso _ _ _ _ (integralSection l E D) (section_isIso l E D).2).symm

/-- The actual section coordinates preserve quotient transitions and completion projections.
Source: reviewed expansion steps 5, 6 and 8
(blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: naturality of constant sheafification gives the first equation. The defining
limit lift of integralConstantToCompletion has the actual quotient cone as its legs,
which gives the second equation after evaluation at the final object. -/
theorem section_reductions (m : ℕ) :
    (∀ a : ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 2)),
      (integralCoefficientSheafTransition l E (Spec (.of D.k)) m).hom.app
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) (finiteSection l E D (m + 1) a) =
          finiteSection l E D m (ULift.up
            (Padic.coefficientExtensionTransition l E (m + 1) a.down))) ∧
    (∀ a : ULift.{u + 1} (Padic.coefficientExtensionIntegers l E),
      (limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op m)).hom.app
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) (integralSection l E D a) =
          finiteSection l E D m (ULift.up
            (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (m + 1)) a.down))) := by
  let U := op (ProEt.mk (𝟙 (Spec (.of D.k))))
  let : EssentiallySmall.{u + 1} (Scheme.ProEt (Spec (.of D.k))) :=
    essentiallySmallSelf.{u} _
  let : HasSheafify (ProEt.topology (Spec (.of D.k))) CommRingCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  let : (sheafToPresheaf (ProEt.topology (Spec (.of D.k)))
      CommRingCat.{u + 1}).IsRightAdjoint :=
    ⟨⟨_, ⟨sheafificationAdjunction _ _⟩⟩⟩
  constructor
  · intro a
    have h := toSheafify_naturality (ProEt.topology (Spec (.of D.k)))
      ((Functor.const (Scheme.ProEt (Spec (.of D.k)))ᵒᵖ).map
        (CommRingCat.ofHom
          ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
            ((Padic.coefficientExtensionTransition l E (m + 1)).comp
              (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom))))
    exact congrArg (fun f ↦ (f.app U).hom a) h.symm
  · intro a
    have h := limit.lift_π (integralConstantCoefficientCone l E (Spec (.of D.k))) (op m)
    have h' := congrArg (fun f ↦ (f.hom.app U)
      (pointConstantSectionMap D.k (Padic.coefficientExtensionIntegers l E) a)) h
    have hn := toSheafify_naturality (ProEt.topology (Spec (.of D.k)))
      ((Functor.const (Scheme.ProEt (Spec (.of D.k)))ᵒᵖ).map
        (CommRingCat.ofHom
          ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
            ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (m + 1))).comp
              (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom))))
    have h'' := congrArg (fun f ↦ (f.app U).hom a) hn.symm
    exact h'.trans h''

variable (Y₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The canonical finite geometric stalk identification, before any Frobenius calculation.
Source: reviewed expansion step 2 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def finiteStalkUnit (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (m : ℕ) :=
  (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.mapIso
    (finiteUnit l E x m) ≪≫ finiteSectionsUnit l E D m

/-- The canonical completed integral geometric stalk identification.
Source: reviewed expansion step 6 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralStalkUnit (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  (pointFibreIntegralAmbient D l E).mapIso (integralUnit l E x) ≪≫ integralSectionsUnit l E D

/-- Iteration of the actual finite Weil maps with the specified pullback compositors.
Source: reviewed expansion step 3 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def finiteWeilIterate (m : ℕ) : (r : ℕ) →
    (finiteDerivedPullback l E m (localPositivePower (D.geometricFrobenius Y₀).hom r)).obj
        (finiteConstantCoefficientObject l E (D.geometricFiber Y₀).left m) ≅
      finiteConstantCoefficientObject l E (D.geometricFiber Y₀).left m
  | 0 => finiteUnit l E (D.geometricFrobenius Y₀).hom m
  | r + 1 =>
    (finiteCanonicalPullbackComposition l E (localPositivePower (D.geometricFrobenius Y₀).hom r)
      (D.geometricFrobenius Y₀).hom m).app _ ≪≫
      (finiteDerivedPullback l E m
        (localPositivePower (D.geometricFrobenius Y₀).hom r)).mapIso
          (finiteUnit l E (D.geometricFrobenius Y₀).hom m) ≪≫ finiteWeilIterate m r

/-- Iterate restriction-and-coprojection transport, retaining the actual finite comparisons.
Source: reviewed expansion step 4 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def finiteTransportIterate (m : ℕ)
    (N : proEtaleDerivedCategory (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (m + 1))) : (r : ℕ) →
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.obj N ⟶
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.obj
        ((finiteDerivedPullback l E m (localPositivePower (frobeniusPointIso D).hom r)).obj N)
  | 0 => frobeniusPointTransportFinite D l hl E m N
  | r + 1 =>
    frobeniusPointTransportFinite D l hl E m N ≫
      finiteTransportIterate m
        ((finiteDerivedPullback l E m (frobeniusPointIso D).hom).obj N) r ≫
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.map
        ((finiteCanonicalPullbackComposition l E (localPositivePower (frobeniusPointIso D).hom r)
          (frobeniusPointIso D).hom m).inv.app N)

/-- The actual local finite operator at a semilinearly returning geometric point.
Source: reviewed expansion step 4 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def finiteOperator (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (m r : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom r =
      localPositivePower (frobeniusPointIso D).hom r ≫ x) :=
  finiteTransportIterate l E D hl m
      ((finiteDerivedPullback l E m x).obj
        (finiteConstantCoefficientObject l E (D.geometricFiber Y₀).left m)) r ≫
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.map
      (((finiteCanonicalPullbackComposition l E
          (localPositivePower (frobeniusPointIso D).hom r) x m).symm.app
          (finiteConstantCoefficientObject l E (D.geometricFiber Y₀).left m) ≪≫
        eqToIso (congrArg (fun (f : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) ↦
          (finiteDerivedPullback l E m f).obj
          (finiteConstantCoefficientObject l E (D.geometricFiber Y₀).left m)) h.symm) ≪≫
        (finiteCanonicalPullbackComposition l E x
          (localPositivePower (D.geometricFrobenius Y₀).hom r) m).app
          (finiteConstantCoefficientObject l E (D.geometricFiber Y₀).left m)).hom) ≫
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.map
      ((finiteDerivedPullback l E m x).map (finiteWeilIterate l E D Y₀ m r).hom)

/-- Contravariant Spec sends the positive power to the corresponding field power.
Source: geometric-Frobenius construction (blueprint: def-weil-local-frobenius-trace). -/
private theorem localPointPower_eq (n : ℕ) :
    localPositivePower (frobeniusPointIso D).hom n =
      let := Fintype.ofFinite D.k₀
      Spec.map (CommRingCat.ofHom
        (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k ^ (n + 1)).toRingHom) := by
  let := Fintype.ofFinite D.k₀
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [localPositivePower, ih]
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 1

/-- Iterating the two Galois-map projections preserves the model projection and
iterates the coefficient projection.
Source: geometric-Frobenius construction (blueprint: def-weil-local-frobenius-trace). -/
private theorem localFrobeniusPower_projections (n : ℕ) :
    localPositivePower (D.geometricFrobenius Y₀).hom n ≫
        pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ∧
    localPositivePower (D.geometricFrobenius Y₀).hom n ≫
        pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫
        localPositivePower (frobeniusPointIso D).hom n := by
  let := Fintype.ofFinite D.k₀
  have h := D.galoisMap_projections Y₀.hom
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)
  change (D.geometricFrobenius Y₀).hom ≫ _ = _ ∧
    (D.geometricFrobenius Y₀).hom ≫ _ =
      _ ≫ (frobeniusPointIso D).hom at h
  induction n with
  | zero => exact h
  | succ n ih =>
    constructor
    · rw [localPositivePower, Category.assoc, h.1]
      exact ih.1
    · rw [localPositivePower, Category.assoc, h.2, ← Category.assoc, ih.2,
        Category.assoc]
      rfl

/-- A model map fixed by the point power has the stated semilinear return lift.
Source: pullback uniqueness in the return construction
(blueprint: def-weil-local-frobenius-trace). -/
private theorem localLift_return (n : ℕ) (a : Spec (.of D.k) ⟶ Y₀.left)
    (c : a ≫ Y₀.hom =
      (𝟙 (Spec (.of D.k))) ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    (ha : localPositivePower (frobeniusPointIso D).hom n ≫ a = a) :
    pullback.lift a (𝟙 _) c ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ pullback.lift a (𝟙 _) c := by
  apply pullback.hom_ext
  · rw [Category.assoc, (localFrobeniusPower_projections D Y₀ n).1,
      pullback.lift_fst, Category.assoc, pullback.lift_fst, ha]
  · rw [Category.assoc, (localFrobeniusPower_projections D Y₀ n).2,
      ← Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd,
      Category.id_comp, Category.comp_id]

/-- Compatibility needed to form the lift for any base-field embedding of the
specified finite extension, rather than only the chosen subfield inclusion.
Source: reviewed expansion step 1 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: functoriality of Spec turns the base-field compatibility of the embedding
into the required equality; compose with the defining Over-morphism equation of x. -/
theorem embeddingPoint_compatible (n : ℕ) (hn : 1 ≤ n)
    (x : D.extensionPoints Y₀ n hn) (ι : D.extensionSubfield n hn →+* D.k)
    (hι : ι.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k) :
    (Spec.map (CommRingCat.ofHom ι) ≫ x.left) ≫ Y₀.hom =
      (𝟙 (Spec (.of D.k))) ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
  rw [Category.assoc, Over.w x, Category.id_comp]
  change Spec.map (CommRingCat.ofHom ι) ≫
    Spec.map (CommRingCat.ofHom (D.extensionEmbedding n hn)) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) hι

/-- The actual geometric point from any allowed finite-field embedding.
Source: reviewed expansion step 1 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def embeddingPoint (n : ℕ) (hn : 1 ≤ n)
    (x : D.extensionPoints Y₀ n hn) (ι : D.extensionSubfield n hn →+* D.k)
    (hι : ι.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k) :
    Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left :=
  pullback.lift (Spec.map (CommRingCat.ofHom ι) ≫ x.left) (𝟙 _)
    (embeddingPoint_compatible D Y₀ n hn x ι hι)

/-- The semilinear return for every base-field embedding into the closure.
Source: reviewed expansion step 1 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: every embedding has image the unique subfield of cardinality q^n. The nth
geometric Frobenius fixes it pointwise. Compare the two projections of the geometric
fiber pullback: the model maps agree by this fixed-field calculation and the closure
maps agree by the geometric Frobenius definition. Pullback uniqueness proves return. -/
theorem embeddingPoint_return (n : ℕ) (hn : 1 ≤ n)
    (x : D.extensionPoints Y₀ n hn) (ι : D.extensionSubfield n hn →+* D.k)
    (hι : ι.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k) :
    embeddingPoint D Y₀ n hn x ι hι ≫
        localPositivePower (D.geometricFrobenius Y₀).hom (n - 1) =
      localPositivePower (frobeniusPointIso D).hom (n - 1) ≫
        embeddingPoint D Y₀ n hn x ι hι := by
  let := Fintype.ofFinite D.k₀
  have hc : Nat.card (D.extensionSubfield n hn) = D.q ^ n :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k n hn).choose_spec.2.1
  have hq : 0 < D.q := by
    rw [← D.card_base]
    exact Nat.card_pos
  have : Finite (D.extensionSubfield n hn) :=
    (Nat.card_pos_iff.mp (by rw [hc]; exact pow_pos hq n)).2
  have hc' : Nat.card (D.extensionSubfield n hn) = Fintype.card D.k₀ ^ n := by
    simpa only [← D.card_base, Nat.card_eq_fintype_card] using hc
  apply localLift_return D Y₀ (n - 1)
  rw [← Category.assoc]
  suffices h : localPositivePower (frobeniusPointIso D).hom (n - 1) ≫
      Spec.map (CommRingCat.ofHom ι) = Spec.map (CommRingCat.ofHom ι) by rw [h]
  rw [localPointPower_eq, Nat.sub_add_cancel hn, ← Spec.map_comp]
  congr 1
  ext a
  exact FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_of_card_eq
    D.k₀ D.k n hc' ι a

attribute [local implicit_reducible] localPositivePower CategoryTheory.Aut

private theorem finiteUnit_eqToHom {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (m : ℕ) :
    eqToHom (congrArg (fun k ↦ (finiteDerivedPullback l E m k).obj
        (finiteConstantCoefficientObject l E Y m)) h) ≫ (finiteUnit l E g m).hom =
      (finiteUnit l E f m).hom := by
  subst g
  simp

private theorem finiteUnit_inv_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (m : ℕ) :
    (finiteCanonicalPullbackComposition l E f g m).inv.app
        (finiteConstantCoefficientObject l E Z m) ≫ (finiteUnit l E (f ≫ g) m).hom =
      (finiteDerivedPullback l E m f).map (finiteUnit l E g m).hom ≫
        (finiteUnit l E f m).hom := by
  rw [← finiteUnit_composition l E f g m]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

private theorem finiteWeilIterate_unit (m r : ℕ) :
    finiteWeilIterate l E D Y₀ m r =
      finiteUnit l E (localPositivePower (D.geometricFrobenius Y₀).hom r) m := by
  induction r with
  | zero => rfl
  | succ r ih =>
    apply Iso.ext
    simpa only [finiteWeilIterate, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, ih,
      localPositivePower]
      using finiteUnit_composition l E
        (localPositivePower (D.geometricFrobenius Y₀).hom r)
        (D.geometricFrobenius Y₀).hom m

private theorem finiteTransportIterate_unit (m r : ℕ)
    (N : proEtaleDerivedCategory (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (m + 1)))
    (a : N ⟶ finiteConstantCoefficientObject l E (Spec (.of D.k)) m) :
    finiteTransportIterate l E D hl m N r ≫
      (pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.map
          ((finiteDerivedPullback l E m
            (localPositivePower (frobeniusPointIso D).hom r)).map a) ≫
      (pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.map
          (finiteUnit l E (localPositivePower (frobeniusPointIso D).hom r) m).hom =
      (pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.map a := by
  let S := (pointFiniteSections D.k
    (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory
  let g := (frobeniusPointIso D).hom
  obtain ⟨τ, hτ⟩ := naturalFiniteTransport D l hl E m
  have base (M : proEtaleDerivedCategory (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (m + 1)))
      (b : M ⟶ finiteConstantCoefficientObject l E (Spec (.of D.k)) m) :
      frobeniusPointTransportFinite D l hl E m M ≫
        S.map ((finiteDerivedPullback l E m g).map b) ≫
        S.map (finiteUnit l E g m).hom = S.map b := by
    have hn := τ.naturality b
    change S.map b ≫ τ.app _ =
      τ.app M ≫ S.map ((finiteDerivedPullback l E m g).map b) at hn
    rw [← hτ M, ← Category.assoc, ← hn, Category.assoc, hτ,
      finitePointTransport_unit l E D hl m, Category.comp_id]
  induction r generalizing N with
  | zero => exact base N a
  | succ r ih =>
    let P := finiteDerivedPullback l E m (localPositivePower g r)
    let G := finiteDerivedPullback l E m g
    let c := finiteCanonicalPullbackComposition l E (localPositivePower g r) g m
    have hc := c.inv.naturality a
    change P.map (G.map a) ≫ c.inv.app _ =
      c.inv.app N ≫ (finiteDerivedPullback l E m (localPositivePower g r ≫ g)).map a at hc
    have hu : c.inv.app (finiteConstantCoefficientObject l E (Spec (.of D.k)) m) ≫
        (finiteUnit l E (localPositivePower g r ≫ g) m).hom =
        P.map (finiteUnit l E g m).hom ≫
          (finiteUnit l E (localPositivePower g r) m).hom := by
      exact finiteUnit_inv_composition l E (localPositivePower g r) g m
    have hnorm : c.inv.app N ≫
        (finiteDerivedPullback l E m (localPositivePower g (r + 1))).map a ≫
        (finiteUnit l E (localPositivePower g (r + 1)) m).hom =
        P.map (G.map a ≫ (finiteUnit l E g m).hom) ≫
          (finiteUnit l E (localPositivePower g r) m).hom := by
      simp only [localPositivePower]
      rw [← Category.assoc, ← hc]
      simp only [Category.assoc, hu, Functor.map_comp]
    change (frobeniusPointTransportFinite D l hl E m N ≫
      finiteTransportIterate l E D hl m (G.obj N) r ≫ S.map (c.inv.app N)) ≫
        S.map ((finiteDerivedPullback l E m (localPositivePower g (r + 1))).map a) ≫
        S.map (finiteUnit l E (localPositivePower g (r + 1)) m).hom = S.map a
    simp only [Category.assoc]
    rw [← S.map_comp, ← S.map_comp, hnorm, S.map_comp]
    rw [ih]
    simpa only [S, G, Functor.map_comp, Category.assoc] using base N a

/-- The finite local operator is the coefficient identity under the canonical stalk iso.
Source: reviewed expansion steps 1--5 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: the image of F_(q^n) is the unique subfield of its order, fixed pointwise by
geometric Frobenius to the nth power. Pullback uniqueness gives the semilinear return,
as in localExtensionPoint_return. Finite unit multiplication sends z tensor b to
c(z)b, commutes with the actual pullback compositor, and identifies the iterated
Weil maps with unit multiplication. Restriction, insertion in the inverse-image
colimit and sheafification all preserve a constant a. The tensor unit and multiplication
then send a to a. Naturality repeats the calculation at every transport in the iterate.
The return square has the same coefficient coordinates on both paths. Thus the entire
local composite is identity, including n=1 and m=0 (exponent one). -/
theorem finiteOperator_unit (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn)
    (ι : D.extensionSubfield n hn →+* D.k)
    (hι : ι.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k) (m : ℕ) :
    finiteOperator l E D hl Y₀ (embeddingPoint D Y₀ n hn x ι hι) m (n - 1)
        (embeddingPoint_return D Y₀ n hn x ι hι) ≫
      (finiteStalkUnit l E D Y₀ (embeddingPoint D Y₀ n hn x ι hι) m).hom =
        (finiteStalkUnit l E D Y₀ (embeddingPoint D Y₀ n hn x ι hι) m).hom := by
  let xbar := embeddingPoint D Y₀ n hn x ι hι
  let h := embeddingPoint_return D Y₀ n hn x ι hι
  let gs := localPositivePower (frobeniusPointIso D).hom (n - 1)
  let gy := localPositivePower (D.geometricFrobenius Y₀).hom (n - 1)
  let B := finiteConstantCoefficientObject l E (D.geometricFiber Y₀).left m
  let S := (pointFiniteSections D.k
    (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory
  have hw :
      (((finiteCanonicalPullbackComposition l E gs xbar m).symm.app B ≪≫
        eqToIso (congrArg (fun f ↦ (finiteDerivedPullback l E m f).obj B) h.symm) ≪≫
        (finiteCanonicalPullbackComposition l E xbar gy m).app B).hom ≫
        (finiteDerivedPullback l E m xbar).map (finiteUnit l E gy m).hom) ≫
        (finiteUnit l E xbar m).hom =
      (finiteDerivedPullback l E m gs).map (finiteUnit l E xbar m).hom ≫
        (finiteUnit l E gs m).hom := by
    simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, eqToIso.hom, Category.assoc]
    rw [finiteUnit_composition l E xbar gy m, finiteUnit_eqToHom l E h.symm m,
      finiteUnit_inv_composition]
  change finiteOperator l E D hl Y₀ xbar m (n - 1) h ≫
    (finiteStalkUnit l E D Y₀ xbar m).hom =
      (finiteStalkUnit l E D Y₀ xbar m).hom
  simp only [finiteOperator, finiteStalkUnit, Iso.trans_hom, Functor.mapIso_hom,
    finiteWeilIterate_unit]
  simp only [Category.assoc]
  simp only [Iso.trans_hom] at hw
  rw [← S.map_comp_assoc, ← S.map_comp_assoc, hw, S.map_comp]
  have ht := congrArg (fun t ↦ t ≫ (finiteSectionsUnit l E D m).hom)
    (finiteTransportIterate_unit l E D hl m (n - 1) _ (finiteUnit l E xbar m).hom)
  simpa only [Category.assoc] using ht

section

-- Keep residue fields abstract when a candidate instance has the wrong source scheme.
attribute [local irreducible] FiniteFieldDatum.geometricFiber Scheme.residueField

private def integralUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    (constructibleIntegralPullback l E f).obj (constantWeilIntegralObject l E D hl Y) ≅
      constantWeilIntegralObject l E D hl X :=
  ObjectProperty.isoMk _ (integralUnit l E f)

private theorem integralUnitIso_composition {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((integralPullbackComposition l E).choose f g).hom.app
        (constantWeilIntegralObject l E D hl Z) ≫
      (constructibleIntegralPullback l E f).map (integralUnitIso l E D hl g).hom ≫
        (integralUnitIso l E D hl f).hom = (integralUnitIso l E D hl (f ≫ g)).hom := by
  apply ObjectProperty.hom_ext
  exact integralUnit_composition_ambient l E D hl f g

private theorem integralUnitIso_eqToHom {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] {f g : X ⟶ Y} (h : f = g) :
    eqToHom (congrArg (fun k ↦ (constructibleIntegralPullback l E k).obj
        (constantWeilIntegralObject l E D hl Y)) h) ≫
      (integralUnitIso l E D hl g).hom = (integralUnitIso l E D hl f).hom := by
  subst g
  simp

private theorem integralUnitIso_inv_composition {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((integralPullbackComposition l E).choose f g).inv.app
        (constantWeilIntegralObject l E D hl Z) ≫
      (integralUnitIso l E D hl (f ≫ g)).hom =
        (constructibleIntegralPullback l E f).map (integralUnitIso l E D hl g).hom ≫
          (integralUnitIso l E D hl f).hom := by
  rw [← integralUnitIso_composition l E D hl f g]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

private theorem integralWeilIterate_unit (r : ℕ) :
    let := sfWeilPrimeInvertible D l hl Y₀
    integralWeilIterate l E D hl Y₀ r =
      integralUnitIso l E D hl (localPositivePower (D.geometricFrobenius Y₀).hom r) := by
  let := sfWeilPrimeInvertible D l hl Y₀
  have ht : constantWeilConstructibleIntegralTheta l E D hl Y₀ =
      integralUnitIso l E D hl (D.geometricFrobenius Y₀).hom := by
    apply Iso.ext
    apply ObjectProperty.hom_ext
    exact congrArg Iso.hom (integralUnit_canonicalWeil l E
      (D.geometricFrobenius Y₀).hom).symm
  induction r with
  | zero => exact ht
  | succ r ih =>
    apply Iso.ext
    simpa only [integralWeilIterate, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, ih,
      localPositivePower, ht] using integralUnitIso_composition l E D hl
        (localPositivePower (D.geometricFrobenius Y₀).hom r)
        (D.geometricFrobenius Y₀).hom

private theorem integralTransportIterate_unit (r : ℕ)
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (a : N ⟶ constantWeilIntegralObject l E D hl (Spec (.of D.k))) :
    let := frobeniusPointPrimeInvertible D l hl
    let S := (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙ pointFibreIntegralAmbient D l E
    integralTransportIterate l E D hl N r ≫
      S.map ((constructibleIntegralPullback l E
        (localPositivePower (frobeniusPointIso D).hom r)).map a) ≫
      S.map (integralUnitIso l E D hl
        (localPositivePower (frobeniusPointIso D).hom r)).hom = S.map a := by
  let := frobeniusPointPrimeInvertible D l hl
  let S := (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙ pointFibreIntegralAmbient D l E
  let g := (frobeniusPointIso D).hom
  obtain ⟨τ, hτ⟩ := naturalIntegralTransport D l hl E
  have base (M : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
      (b : M ⟶ constantWeilIntegralObject l E D hl (Spec (.of D.k))) :
      frobeniusPointTransportIntegral D l hl E M.obj ≫
        S.map ((constructibleIntegralPullback l E g).map b) ≫
        S.map (integralUnitIso l E D hl g).hom = S.map b := by
    have hn := τ.naturality b.hom
    change S.map b ≫ τ.app _ =
      τ.app M.obj ≫ S.map ((constructibleIntegralPullback l E g).map b) at hn
    rw [← hτ M.obj, ← Category.assoc, ← hn, Category.assoc, hτ]
    change S.map b ≫ (frobeniusPointTransportIntegral D l hl E
      (integralConstantCoefficientObject l E (Spec (.of D.k))) ≫
      (pointFibreIntegralAmbient D l E).map (integralUnit l E g).hom) = _
    rw [integralPointTransport_unit]
    exact Category.comp_id _
  induction r generalizing N with
  | zero => exact base N a
  | succ r ih =>
    let P := constructibleIntegralPullback l E (localPositivePower g r)
    let G := constructibleIntegralPullback l E g
    let c := (integralPullbackComposition l E).choose (localPositivePower g r) g
    have hc := c.inv.naturality a
    change P.map (G.map a) ≫ c.inv.app _ =
      c.inv.app N ≫ (constructibleIntegralPullback l E (localPositivePower g r ≫ g)).map a
      at hc
    have hu : c.inv.app (constantWeilIntegralObject l E D hl (Spec (.of D.k))) ≫
        (integralUnitIso l E D hl (localPositivePower g r ≫ g)).hom =
      P.map (integralUnitIso l E D hl g).hom ≫
        (integralUnitIso l E D hl (localPositivePower g r)).hom :=
      integralUnitIso_inv_composition l E D hl (localPositivePower g r) g
    have hnorm : c.inv.app N ≫
        (constructibleIntegralPullback l E (localPositivePower g (r + 1))).map a ≫
        (integralUnitIso l E D hl (localPositivePower g (r + 1))).hom =
      P.map (G.map a ≫ (integralUnitIso l E D hl g).hom) ≫
        (integralUnitIso l E D hl (localPositivePower g r)).hom := by
      simp only [localPositivePower]
      rw [← Category.assoc, ← hc]
      simp only [Category.assoc, hu, Functor.map_comp]
    change (frobeniusPointTransportIntegral D l hl E N.obj ≫
      integralTransportIterate l E D hl (G.obj N) r ≫ S.map (c.inv.app N)) ≫
        S.map ((constructibleIntegralPullback l E (localPositivePower g (r + 1))).map a) ≫
        S.map (integralUnitIso l E D hl (localPositivePower g (r + 1))).hom = S.map a
    simp only [Category.assoc]
    rw [← S.map_comp, ← S.map_comp, hnorm, S.map_comp]
    rw [ih]
    simpa only [S, G, Functor.map_comp, Category.assoc] using base N a

/-- The completed integral local operator is identity on the whole derived stalk.
Source: reviewed expansion steps 1, 6 and 7 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: the integral regular module is a flat-term K-flat model. Its finite reductions
are the regular quotient modules with the actual quotient transitions. The compatible
finite multiplication maps identify its pulled strict tower with the coefficient tower
at s. The zero-shifted-component comparison identifies the whole Roos complex with
the completed integral unit. Sectionwise limits and completeness identify sections
with O_E, and all projections with the quotient maps. The normalized inverse-image
comparison and whole-system point-transport power laws identify the actual integral
local operator with this reconstructed finite identity. This uses equality of strict
system maps and their normalized cone maps, not detection by unrelated finite reductions. -/
theorem integralOperator_unit (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn)
    (ι : D.extensionSubfield n hn →+* D.k)
    (hι : ι.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k) :
    integralOperator l E D hl Y₀ (embeddingPoint D Y₀ n hn x ι hι) (n - 1)
        (embeddingPoint_return D Y₀ n hn x ι hι) ≫
      (integralStalkUnit l E D Y₀ (embeddingPoint D Y₀ n hn x ι hι)).hom =
        (integralStalkUnit l E D Y₀ (embeddingPoint D Y₀ n hn x ι hι)).hom := by
  let := sfWeilPrimeInvertible D l hl Y₀
  let := frobeniusPointPrimeInvertible D l hl
  let xbar := embeddingPoint D Y₀ n hn x ι hι
  let h := embeddingPoint_return D Y₀ n hn x ι hι
  let gs := localPositivePower (frobeniusPointIso D).hom (n - 1)
  let gy := localPositivePower (D.geometricFrobenius Y₀).hom (n - 1)
  let B := constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left
  let S := (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙ pointFibreIntegralAmbient D l E
  let v := ((integralPullbackComposition l E).choose gs xbar).symm.app B ≪≫
    eqToIso (congrArg (fun f ↦ (constructibleIntegralPullback l E f).obj B) h.symm) ≪≫
    ((integralPullbackComposition l E).choose xbar gy).app B
  have hw :
      (v.hom ≫
        (constructibleIntegralPullback l E xbar).map (integralUnitIso l E D hl gy).hom) ≫
        (integralUnitIso l E D hl xbar).hom =
      (constructibleIntegralPullback l E gs).map (integralUnitIso l E D hl xbar).hom ≫
        (integralUnitIso l E D hl gs).hom := by
    simp only [v, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, eqToIso.hom, Category.assoc]
    rw [integralUnitIso_composition l E D hl xbar gy,
      integralUnitIso_eqToHom l E D hl h.symm, integralUnitIso_inv_composition]
  change integralOperator l E D hl Y₀ xbar (n - 1) h ≫
    (integralStalkUnit l E D Y₀ xbar).hom = (integralStalkUnit l E D Y₀ xbar).hom
  simp only [integralOperator, integralStalkUnit, Iso.trans_hom, Functor.mapIso_hom,
    integralWeilIterate_unit, Category.assoc]
  change integralTransportIterate l E D hl
    ((constructibleIntegralPullback l E xbar).obj B) (n - 1) ≫ S.map v.hom ≫
      S.map ((constructibleIntegralPullback l E xbar).map
      (integralUnitIso l E D hl gy).hom) ≫ S.map (integralUnitIso l E D hl xbar).hom ≫
      (integralSectionsUnit l E D).hom =
    S.map (integralUnitIso l E D hl xbar).hom ≫ (integralSectionsUnit l E D).hom
  rw [← S.map_comp_assoc, ← S.map_comp_assoc, hw, S.map_comp]
  have ht := congrArg (fun t ↦ t ≫ (integralSectionsUnit l E D).hom)
    (integralTransportIterate_unit l E D hl (n - 1)
      ((constructibleIntegralPullback l E xbar).obj B) (integralUnitIso l E D hl xbar).hom)
  simpa only [Category.assoc] using ht


end

/-- The fraction-field tensor of the regular integral module is the regular field module.
Source: reviewed expansion step 8 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def rationalRegular :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E)).obj
        (ModuleCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) ≅
      ModuleCat.of (ULift.{u + 1} E) (ULift.{u + 1} E) :=
  letI := (pointIntegralToField l E).toAlgebra
  (TensorProduct.AlgebraTensorModule.rid (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
    (ULift.{u + 1} E) (ULift.{u + 1} E)).toModuleIso

/-- The canonical large rational unit identification, obtained by tensoring the integral one.
Source: reviewed expansion step 8 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def rationalStalkUnitLarge (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  rationalFibreComparison l E D hl Y₀ x ≪≫
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (pointIntegralToField l E)).mapDerivedCategory.mapIso (integralStalkUnit l E D Y₀ x) ≪≫
    ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (pointIntegralToField l E)).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (rationalRegular l E) ≪≫
    ((pointFibreModuleLift E).mapDerivedCategorySingleFunctor 0).symm.app (ModuleCat.of E E)

/-- The small rational unit is uniquely determined by its actual scalar-normalization square.
Source: reviewed expansion step 8 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: the large map is integral unit multiplication tensor E, with the specified
rational object comparisons and size-descent counit. Its source and target have bounded
finite-dimensional cohomology. The equivalence pointFibreSizeLift is fully faithful
on this subcategory, so the large map and its inverse descend uniquely. Faithfulness
reflects both inverse equations. This gives a unique isomorphism with the displayed
normalization, not an arbitrary choice of a point-unit isomorphism. -/
theorem rationalStalkUnit_existsUnique
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :
    ∃! e : (localPointComplex l E D hl Y₀
        (constantWeilRationalComplex l E D hl Y₀) x).obj ≅
          (DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of E E),
      (pointFibreModuleLift E).mapDerivedCategory.mapIso e =
        rationalStalkUnitLarge l E D hl Y₀ x := by
  classical
  let p := DerivedCategory.pointFiniteDimensional E
  let q := DerivedCategory.pointFiniteDimensional (ULift.{u + 1} E)
  let J := p.ι ⋙ (pointFibreModuleLift E).mapDerivedCategory
  let := pointFibreSizeLift_equivalence E
  let J₀ := pointFibreSizeLift E ⋙ q.ι
  let eJ : J₀ ≅ J :=
    q.liftCompιIso (p.ι ⋙ (pointFibreModuleLift E).mapDerivedCategory)
      (pointFibreModuleLift_mem E)
  have : J₀.Full := by dsimp only [J₀]; infer_instance
  have : J₀.Faithful := by dsimp only [J₀]; infer_instance
  let ff := (Functor.FullyFaithful.ofFullyFaithful J₀).ofIso eJ
  have : J.Full := ff.full
  have : J.Faithful := ff.faithful
  let V := (DerivedCategory.singleFunctor (ModuleCat.{u} E) 0).obj (ModuleCat.of E E)
  have hV : p V := by
    refine ⟨⟨{0}, fun i hi ↦ ?_⟩, fun i ↦ ?_⟩
    · exact DerivedCategory.isZero_homologyFunctor_obj_of_iso_singleFunctor
        (Iso.refl V) (by simpa only [Finset.mem_singleton] using hi)
    · by_cases hi : i = 0
      · subst i
        let e₀ : (DerivedCategory.homologyFunctor (ModuleCat.{u} E) 0).obj V ≅
            ModuleCat.of E E :=
          (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} E) 0).app _
        exact e₀.symm.toLinearEquiv.finiteDimensional
      · have hz := DerivedCategory.isZero_homologyFunctor_obj_of_iso_singleFunctor
          (Iso.refl V) hi
        have := ModuleCat.isZero_iff_subsingleton.mp hz
        infer_instance
  let X : p.FullSubcategory := localPointComplex l E D hl Y₀
    (constantWeilRationalComplex l E D hl Y₀) x
  let Y : p.FullSubcategory := ⟨V, hV⟩
  let a : J.obj X ≅ J.obj Y := rationalStalkUnitLarge l E D hl Y₀ x
  let e : X ≅ Y := J.preimageIso a
  refine ⟨p.ι.mapIso e, ?_, ?_⟩
  · change J.mapIso e = a
    ext
    exact J.map_preimage a.hom
  · intro e' he'
    let b : X ≅ Y := p.ι.preimageIso e'
    have hb : J.mapIso b = a := by
      change (pointFibreModuleLift E).mapDerivedCategory.mapIso (p.ι.mapIso b) = a
      have h : p.ι.mapIso b = e' := by
        ext
        exact p.ι.map_preimage (X := X) (Y := Y) e'.hom
      rw [h]
      exact he'
    have he : J.mapIso e = a := by ext; exact J.map_preimage a.hom
    have hbe : b = e := J.mapIso_injective (hb.trans he.symm)
    calc
      e' = p.ι.mapIso b := by
        ext
        exact (p.ι.map_preimage (X := X) (Y := Y) e'.hom).symm
      _ = p.ι.mapIso e := congrArg (fun t ↦ p.ι.mapIso t) hbe

/-- The rational geometric stalk identification with E[0], normalized by integral tensor.
Source: reviewed expansion step 8 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def rationalStalkUnit (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  (rationalStalkUnit_existsUnique l E D hl Y₀ x).exists.choose

/-- The actual rational operator is tensor of the actual integral operator, under
the prescribed rational point comparison, so rationalization respects operator equality.
Source: reviewed expansion step 8 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: localPullbackObjectIso identifies the underlying integral objects. The rational
Weil map, composition maps and transport are the localized integral maps. Naturality
of the size-descent counit then identifies each factor of the two local composites.
Exact scalar extension preserves their composition, yielding the displayed square. -/
theorem rationalOperator_scalar (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (r : ℕ) (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom r =
      localPositivePower (frobeniusPointIso D).hom r ≫ x) :
    (pointFibreModuleLift E).mapDerivedCategory.map
        (localFrobeniusOperator l E D hl Y₀
          (constantWeilRationalComplex l E D hl Y₀) x r h).hom ≫
      (rationalFibreComparison l E D hl Y₀ x).hom =
        (rationalFibreComparison l E D hl Y₀ x).hom ≫
          (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
            (pointIntegralToField l E)).mapDerivedCategory.map
              (integralOperator l E D hl Y₀ x r h) := by
  let := sfWeilPrimeInvertible D l hl Y₀
  let := frobeniusPointPrimeInvertible D l hl
  let L := (pointFibreModuleLift E).mapDerivedCategory
  let T := (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
    (pointIntegralToField l E)).mapDerivedCategory
  let K := constantWeilRationalComplex l E D hl Y₀
  let a := localPointTransportIterate l E D hl (localDerivedStalk l E D hl Y₀ K x) r
  let b := (pointRationalFibre D l hl E).map
    ((localReturnComparison l E D hl Y₀ K x r h).hom ≫
      (rationalDerivedPullback l E x).map (localWeilIterate l E D hl Y₀ K r).hom)
  have hab : (localFrobeniusOperator l E D hl Y₀ K x r h).hom =
      a.hom ≫ b.hom := by
    simp only [localFrobeniusOperator, a, b, Functor.map_comp,
      ObjectProperty.FullSubcategory.comp_hom]
  rw [hab, L.map_comp, Category.assoc, returnWeil_integral_scalar]
  rw [← Category.assoc, pointTransport_integral_scalar, Category.assoc,
    ← T.map_comp]
  rfl


/-- The rational local operator is identity in the same canonical coefficient coordinates.
Source: reviewed expansion steps 1 and 8 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: theta_E and rational point transport are the images of their integral counterparts
under exact tensor with E, with the recorded boundary comparisons. The rational pullback
compositors are the localized integral ones, so all three factors of localFrobeniusOperator
are the corresponding integral factors after tensor. Apply integralOperator_unit to the
whole-system identity, tensor it with E, and cancel the specified size equivalence. The
normalization of rationalStalkUnit makes its coefficient coordinate exactly E[0]. -/
theorem rationalOperator_unit (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn)
    (ι : D.extensionSubfield n hn →+* D.k)
    (hι : ι.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k) :
    (localFrobeniusOperator l E D hl Y₀
        (constantWeilRationalComplex l E D hl Y₀)
        (embeddingPoint D Y₀ n hn x ι hι) (n - 1)
        (embeddingPoint_return D Y₀ n hn x ι hι)).hom ≫
      (rationalStalkUnit l E D hl Y₀ (embeddingPoint D Y₀ n hn x ι hι)).hom =
        (rationalStalkUnit l E D hl Y₀ (embeddingPoint D Y₀ n hn x ι hι)).hom := by
  let xbar := embeddingPoint D Y₀ n hn x ι hι
  let hreturn := embeddingPoint_return D Y₀ n hn x ι hι
  have hI : integralOperator l E D hl Y₀ xbar (n - 1) hreturn = 𝟙 _ := by
    apply (cancel_mono (integralStalkUnit l E D Y₀ xbar).hom).mp
    simpa only [Category.id_comp] using integralOperator_unit l E D hl Y₀ n hn x ι hι
  let := pointFibreSizeLift_equivalence E
  have hR : localFrobeniusOperator l E D hl Y₀
      (constantWeilRationalComplex l E D hl Y₀) xbar (n - 1) hreturn = 𝟙 _ := by
    apply (pointFibreSizeLift E).map_injective
    rw [CategoryTheory.Functor.map_id]
    apply ObjectProperty.hom_ext
    change (pointFibreModuleLift E).mapDerivedCategory.map
      (localFrobeniusOperator l E D hl Y₀
        (constantWeilRationalComplex l E D hl Y₀) xbar (n - 1) hreturn).hom = 𝟙 _
    apply (cancel_mono (rationalFibreComparison l E D hl Y₀ xbar).hom).mp
    rw [rationalOperator_scalar, hI]
    simp only [Category.id_comp]
    exact (congrArg (fun t ↦ (rationalFibreComparison l E D hl Y₀ xbar).hom ≫ t)
      ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)).mapDerivedCategory.map_id _)).trans (Category.comp_id _)
  change (localFrobeniusOperator l E D hl Y₀
    (constantWeilRationalComplex l E D hl Y₀) xbar (n - 1) hreturn).hom ≫ _ = _
  rw [hR]
  exact Category.id_comp _


end WeilConjectures.ConstantGeometricStalkUnit
