/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.SmoothPurity.Derived.DerivedCompleteIntegralDetailed
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExact
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientComplexRationalization
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.PoincareDuality.CompletedScalarExtensionTExact
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import all WeilConjectures.SmoothPurity.PointDerivedSectionsTensor.PointDerivedSectionsTensorDescent
import all WeilConjectures.CategoryTheory.Finite.FiniteFreeStrictTowerTransport
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import all WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import all WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import all WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import all Mathlib.CategoryTheory.Filtered.Basic
import all Mathlib.CategoryTheory.Limits.Cones
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import all WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Adjunction.CompositionIso
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSiteColimits
import all WeilConjectures.TraceFormula.Supporting.PointFiniteReductionSectionAlgebra
public import WeilConjectures.AlgebraicGeometry.Picard.SuccessiveDerivedQuotientNormalization
public import WeilConjectures.SmoothPurity.SheafRingCoefficientOrdinaryAdjunction

/-! # Sections of the geometric point and integral coefficient extension

Source: blueprint `def-weil-finite-coefficient-point`, final paragraph;
Bhatt--Scholze, Lemmas 4.2.12, 6.8.2(1), Definition 3.4.10 and Lemma 3.4.12
(blueprint: lem-weil-point-sections-scalar-extension).

All tensors on coefficient modules below are ordinary termwise tensors. The
sections-tensor arrow is fixed on pure tensors, and the derived arrow is fixed
on every K-flat flat-term representative. Completion uses the recorded strict
zero-homotopy comparison, rather than an unspecified derived-limit lift.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u a b c d e f

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace WeilConjectures

attribute [local irreducible] limit HasDerivedCategory.standard

attribute [-instance] WeilConjectures.podCompletedOrdinaryScalarExtension_preservesFiniteLimits
  WeilConjectures.podCompletedOrdinaryScalarExtension_preservesFiniteColimits

  WeilConjectures.coefficientComplexIntegralLimits
  WeilConjectures.coefficientComplexIntegralColimits
  WeilConjectures.coefficientComplexRationalAdditive
  WeilConjectures.coefficientComplexRationalLimits
  WeilConjectures.coefficientComplexRationalColimits
  WeilConjectures.coefficientComplexFieldAdditive
  WeilConjectures.coefficientComplexFieldLimits
  WeilConjectures.coefficientComplexFieldColimits
  WeilConjectures.coefficientComplexModuleDerived

variable (k : Type u) [Field k] [IsAlgClosed k]
  (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The recorded locally bijective criterion at the point's actual module size.
Source: Stacks 03DA (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance (priority := 5000) pointScalarAbLocallyBijective :
    (Scheme.ProEt.topology (Spec (.of k))).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} (Spec (.of k))

/-- Standard localization of coefficient-module complexes in the section universe.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointScalarModuleDerived (A : Type u) [Ring A] :
    HasDerivedCategory (ModuleCat.{u + 1} A) := HasDerivedCategory.standard _

/-- Standard localization for modules on the point in their actual section universe.
Source: Stacks 05RU (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCompletedSheafDerived
    (R : Sheaf (Scheme.ProEt.topology (Spec (.of k))) RingCat.{u + 1}) :
    HasDerivedCategory (SheafOfModules.{u + 1} R) := HasDerivedCategory.standard _

/-- The canonical constant-section coefficient map at the final object, obtained
from the recorded constant-to-completion morphism and sheafification unit.
Source: Bhatt--Scholze 6.8.2(1); blueprint completed coefficients, order 1455
(blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointCompletedConstant :
    Padic.coefficientExtensionIntegers l E →+*
      (completedIntegralCoefficientSheafUnrestricted.{u, u} l E (Spec (.of k))).obj.obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) :=
  (((integralConstantToCompletion l E (Spec (.of k))).hom.app
    (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))).hom).comp
      ((((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        ((toSheafify (Scheme.ProEt.topology (Spec (.of k)))
          ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))))).app
              (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))).hom).comp
                ULift.ringEquiv.symm.toRingHom)

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
omit [IsAlgClosed k] in
private theorem pointCompletedConstant_projection (n : ℕ)
    (a : Padic.coefficientExtensionIntegers l E) :
    ((limit.π (integralCoefficientSheafSystem l E (Spec (.of k))) (op n)).hom.app
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) (pointCompletedConstant k l E a) =
        integralScalarFiniteConstant l E (Spec (.of k)) n
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) a := by
  let : EssentiallySmall.{u + 1} (Scheme.ProEt (Spec (.of k))) := essentiallySmallSelf.{u} _
  let : HasSheafify (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  let : (sheafToPresheaf (Scheme.ProEt.topology (Spec (.of k)))
      CommRingCat.{u + 1}).IsRightAdjoint := ⟨⟨_, ⟨sheafificationAdjunction _ _⟩⟩⟩
  let Y := Spec (.of k)
  let U := op (Scheme.ProEt.mk (𝟙 Y))
  have h := congrArg (fun f ↦ f.hom.app U
    (((toSheafify (Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))))).app U) (ULift.up a)))
    (limit.lift_π (integralConstantCoefficientCone l E Y) (op n))
  change _ = _ at h
  change _ = _
  refine h.trans ?_
  have hn := toSheafify_naturality (Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).map (CommRingCat.ofHom
        ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
          ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
            (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom))))
  exact congrArg (fun f ↦ (f.app U).hom (ULift.up a)) hn.symm

private theorem bijectiveFromCompatibleCoordinates
    {R : Type a} {S : Type b} {A : ℕ → Type c} {B : ℕ → Type d}
    (transition : ∀ n, A (n + 1) → A n)
    (T : Type e) (q : R ≃ T) (coordinates : T → ∀ n, A n)
    (hcoords : Function.Injective coordinates)
    (mk : ∀ v : ∀ n, A n, (∀ n, transition n (v (n + 1)) = v n) → T)
    (hmk : ∀ v h, coordinates (mk v h) = v)
    (f : R → S) (p : ∀ n, S → B n) (ep : ∀ n, A n ≃ B n)
    (hp : ∀ x y, (∀ n, p n x = p n y) → x = y)
    (hf : ∀ n x, p n (f x) = ep n (coordinates (q x) n))
    (hc : ∀ s n, transition n ((ep (n + 1)).symm (p (n + 1) s)) =
      (ep n).symm (p n s)) : Function.Bijective f := by
  constructor
  · intro x y h
    apply q.injective
    apply hcoords
    funext n
    apply (ep n).injective
    rw [← hf, h, hf]
  · intro s
    let t := mk (fun n ↦ (ep n).symm (p n s)) (hc s)
    refine ⟨q.symm t, ?_⟩
    apply hp
    intro n
    rw [hf, q.apply_symm_apply]
    change ep n (coordinates (mk _ _) n) = p n s
    rw [hmk]
    exact (ep n).apply_symm_apply _

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem pointCompletedConstant_bijective :
    Function.Bijective (pointCompletedConstant k l E) := by
  let : EssentiallySmall.{u + 1} (Scheme.ProEt (Spec (.of k))) := essentiallySmallSelf.{u} _
  let : HasSheafify (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  classical
  let : (sheafToPresheaf (Scheme.ProEt.topology (Spec (.of k)))
      CommRingCat.{u + 1}).IsRightAdjoint := ⟨⟨_, ⟨sheafificationAdjunction _ _⟩⟩⟩
  let Y := Spec (.of k)
  let U := op (Scheme.ProEt.mk (𝟙 Y))
  let A := fun n ↦ Padic.coefficientExtensionRing l E (n + 1)
  let c (n : ℕ) : ULift.{u + 1} (A n) →+* (integralCoefficientSheaf l E Y n).obj.obj U :=
    ((forget₂ CommRingCat RingCat).map
      ((toSheafify (Scheme.ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} (A n))))).app U)).hom
  have hc (n : ℕ) : Function.Bijective (c n) :=
    AlgebraicGeometry.ProEtale.bijective_toSheafify_app_of_iso (Iso.refl _)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} (A n))))
  let e (n : ℕ) := RingEquiv.ofBijective (c n) (hc n)
  let π (n : ℕ) : (limit (integralCoefficientSheafSystem l E Y)).obj.obj U ⟶
      (integralCoefficientSheaf l E Y n).obj.obj U :=
    (limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app U
  have hπ (n : ℕ) (a : Padic.coefficientExtensionIntegers l E) :
      π n (pointCompletedConstant k l E a) =
        e n (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a)) :=
    pointCompletedConstant_projection k l E n a
  obtain ⟨q, hq, _⟩ := (Padic.coefficientExtension_integers_profinite_tower.{u, 0} l E).1
  have hc (s : (limit (integralCoefficientSheafSystem l E Y)).obj.obj U) (n : ℕ) :
    Padic.coefficientExtensionTransition l E (n + 1)
      (((e (n + 1)).symm (π (n + 1) s)).down) = ((e n).symm (π n s)).down := by
    apply ULift.up_injective
    apply (e n).injective
    have hn := toSheafify_naturality (Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).map (CommRingCat.ofHom
        ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
          ((Padic.coefficientExtensionTransition l E (n + 1)).comp
            (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom))))
    have hn' := congrArg (fun f ↦ (f.app U).hom ((e (n + 1)).symm (π (n + 1) s))) hn
    have hw := congrArg (fun f ↦ f.hom.app U s)
      (limit.w (integralCoefficientSheafSystem l E Y) (homOfLE (Nat.le_succ n)).op)
    simp only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ] at hw
    change e n (ULift.up (Padic.coefficientExtensionTransition l E (n + 1)
      (((e (n + 1)).symm (π (n + 1) s)).down))) =
      (integralCoefficientSheafTransition l E Y n).hom.app U
        (e (n + 1) ((e (n + 1)).symm (π (n + 1) s))) at hn'
    have he := congrArg ((integralCoefficientSheafTransition l E Y n).hom.app U)
      ((e (n + 1)).apply_symm_apply (π (n + 1) s))
    have hw' : (integralCoefficientSheafTransition l E Y n).hom.app U (π (n + 1) s) =
        π n s := hw
    exact hn'.trans (he.trans (hw'.trans ((e n).apply_symm_apply _).symm))
  apply bijectiveFromCompatibleCoordinates
    (fun n ↦ Padic.coefficientExtensionTransition l E (n + 1))
    (Padic.coefficientExtensionPositiveLimit l E) q.toEquiv
    (fun t ↦ t.val) (fun _ _ h ↦ Subtype.ext h)
    (fun v hv ↦ ⟨v, by
      simp only [Padic.coefficientExtensionPositiveLimit, Subring.mem_iInf,
        RingHom.mem_eqLocus, RingHom.comp_apply, Pi.evalRingHom_apply]
      exact hv⟩) (fun _ _ ↦ rfl) (pointCompletedConstant k l E) (fun n s ↦ π n s)
    (fun n ↦ (Equiv.ulift.symm).trans (e n).toEquiv)
  · intro x y h
    apply ringSheafLimit_ext (integralCoefficientSheafSystem l E Y) U
    intro n
    exact h n.unop
  · intro n x
    rw [hπ]
    change e n (ULift.up _) = e n (ULift.up ((q x).val n))
    rw [hq]
  · exact hc

omit [IsAlgClosed k] in
private theorem pointCompletedConstant_eq (a : Padic.coefficientExtensionIntegers l E) :
    pointCompletedConstant k l E a = integralScalarConstant l E (Spec (.of k))
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) a := by
  apply (integralScalarConstant_existsUnique l E (Spec (.of k))
    (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) a).unique
  · intro n
    exact pointCompletedConstant_projection k l E n a
  · exact (integralScalarConstant_existsUnique l E (Spec (.of k))
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) a).exists.choose_spec

/-- Evaluation, with coefficients restricted along the actual constant-section map.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable abbrev pointCompletedSections :
    integralTowerModules.{u, u} l E (Spec (.of k)) ⥤
      ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E) :=
  SheafOfModules.evaluation.{u + 1}
      (completedIntegralCoefficientSheafUnrestricted.{u, u} l E (Spec (.of k)))
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) ⋙
    ModuleCat.restrictScalars (pointCompletedConstant k l E)

/-- Exactness and additivity of completed integral sections.
Source: exact point-sections node and blueprint final paragraph
(blueprint: lem-weil-point-sections-scalar-extension).
Proof: point evaluation is exact by lem-weil-point-proetale-sections-exact.
Restriction of scalars leaves the underlying abelian group unchanged, so preserves
kernels and cokernels. Both functors add maps sectionwise. -/
theorem pointCompletedSections_exact :
    (pointCompletedSections k l E).Additive ∧
      PreservesFiniteLimits (pointCompletedSections k l E) ∧
      PreservesFiniteColimits (pointCompletedSections k l E) := by
  have h := (AlgebraicGeometry.ProEtale.point_proEtale_sections_exact.{u, u + 2, u + 2} k).2
    (completedIntegralCommRingSheafUnrestricted.{u, u} l E (Spec (.of k)))
  have : PreservesFiniteLimits
      (SheafOfModules.evaluation.{u + 1}
        (completedIntegralCoefficientSheafUnrestricted.{u, u} l E (Spec (.of k)))
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) := h.1
  have : PreservesFiniteColimits
      (SheafOfModules.evaluation.{u + 1}
        (completedIntegralCoefficientSheafUnrestricted.{u, u} l E (Spec (.of k)))
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) := h.2.1
  let T := ModuleCat.restrictScalars.{u + 1} (pointCompletedConstant k l E)
  have : PreservesFiniteLimits T := by
    constructor
    intro J _ _
    constructor
    intro F
    exact ModuleCat.preservesLimit_restrictScalars (pointCompletedConstant k l E) F
  have : PreservesFiniteColimits T := by
    constructor
    intro J _ _
    constructor
    intro F
    exact ModuleCat.preservesColimit_restrictScalars (pointCompletedConstant k l E) F
  refine ⟨?_, comp_preservesFiniteLimits _ T, comp_preservesFiniteColimits _ T⟩
  exact ⟨by intros; rfl⟩

/-- Additivity supplied by exact evaluation.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCompletedSectionsAdditive :
    (pointCompletedSections k l E).Additive := (pointCompletedSections_exact k l E).1

/-- Finite-limit preservation supplied by exact evaluation.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCompletedSectionsLimits :
    PreservesFiniteLimits (pointCompletedSections k l E) :=
  (pointCompletedSections_exact k l E).2.1

/-- Finite-colimit preservation supplied by exact evaluation.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCompletedSectionsColimits :
    PreservesFiniteColimits (pointCompletedSections k l E) :=
  (pointCompletedSections_exact k l E).2.2

/-- Termwise completed sections, descended through derived localization.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable abbrev pointCompletedDerivedSections :
    DerivedCategory (integralTowerModules.{u, u} l E (Spec (.of k))) ⥤
      DerivedCategory (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) :=
  (pointCompletedSections k l E).mapDerivedCategory

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Ordinary tensor with the valuation ring of the larger coefficient field.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable abbrev pointIntegralModuleTensor :=
  ModuleCat.extendScalars.{u, u, u + 1} (integralScalarIntegerInclusion.{u} l E L ι)

/-- The ordinary module tensor and fraction-field tensor functors are exact and additive.
Source: Bhatt--Scholze 6.8.2(1), blueprint final paragraph
(blueprint: lem-weil-point-sections-scalar-extension).
Proof: O_L is finite free over O_E, so tensor is a finite direct sum, hence exact.
The fraction field of a valuation DVR is its localization at nonzero elements;
localization preserves kernels and cokernels. The tensor maps add termwise. -/
theorem pointCoefficientTensors_exact :
    ((pointIntegralModuleTensor l E L ι).Additive ∧
      PreservesFiniteLimits (pointIntegralModuleTensor l E L ι) ∧
      PreservesFiniteColimits (pointIntegralModuleTensor l E L ι)) ∧
    ((ModuleCat.extendScalars.{u, u, u + 1}
      (algebraMap (Padic.coefficientExtensionIntegers l E) E)).Additive ∧
      PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u + 1}
        (algebraMap (Padic.coefficientExtensionIntegers l E) E)) ∧
      PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u + 1}
        (algebraMap (Padic.coefficientExtensionIntegers l E) E))) := by
  exact ⟨(coefficientComplexTensors_exact.{u, u + 1} l E L ι).1,
    (coefficientComplexTensors_exact.{u, u + 1} l E L ι).2.1⟩

/-- Additivity of the ordinary integral tensor.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointIntegralModuleTensorAdditive :
    (pointIntegralModuleTensor l E L ι).Additive :=
  (pointCoefficientTensors_exact l E L ι).1.1

/-- Exactness at kernels of the ordinary integral tensor.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointIntegralModuleTensorLimits :
    PreservesFiniteLimits (pointIntegralModuleTensor l E L ι) :=
  (pointCoefficientTensors_exact l E L ι).1.2.1

/-- Exactness at cokernels of the ordinary integral tensor.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointIntegralModuleTensorColimits :
    PreservesFiniteColimits (pointIntegralModuleTensor l E L ι) :=
  (pointCoefficientTensors_exact l E L ι).1.2.2

/-- Ordinary termwise integral tensor on module derived categories.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable abbrev pointIntegralModuleDerivedTensor :=
  (pointIntegralModuleTensor l E L ι).mapDerivedCategory

omit [IsAlgClosed k] in
private theorem pointCompletedConstant_compatibility
    (a : Padic.coefficientExtensionIntegers l E) :
    (completedCoefficientMap l E L ι (Spec (.of k))).hom.app
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) (pointCompletedConstant k l E a) =
      pointCompletedConstant k l L (integralScalarIntegerInclusion l E L ι a) := by
  rw [pointCompletedConstant_eq, pointCompletedConstant_eq]
  apply (integralScalarConstant_existsUnique l L (Spec (.of k))
    (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))
      (integralScalarIntegerInclusion l E L ι a)).unique
  · intro n
    have h := congrArg (fun f ↦ f.hom.app
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))
        (integralScalarConstant l E (Spec (.of k))
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) a))
      (completedCoefficientMap_projection l E L ι (Spec (.of k)) n)
    exact h.trans (integralScalarRho_constant l E L ι (Spec (.of k)) n _ a)
  · exact (integralScalarConstant_existsUnique l L (Spec (.of k))
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))
        (integralScalarIntegerInclusion l E L ι a)).exists.choose_spec

private noncomputable def pointTensorSquareIso
    {A B : Type u} {R S : Type (u + 1)}
    [CommRing A] [CommRing B] [CommRing R] [CommRing S]
    (f : A →+* B) (g : R →+* S) (en : A ≃+* R) (ej : B ≃+* S)
    (hs : ∀ a, ej (f a) = g (en a)) (N : ModuleCat.{u + 1} R) :
    (ModuleCat.extendScalars.{u, u, u + 1} f).obj
        ((ModuleCat.restrictScalars (en : A →+* R)).obj N) ≅
      (ModuleCat.restrictScalars (ej : B →+* S)).obj
        ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} g).obj N) := by
  letI := g.toAlgebra
  letI := RingHomInvPair.of_ringEquiv en
  letI := RingHomInvPair.symm (en : A →+* R) (en.symm : R →+* A)
  let e₁ : ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) ≃ₛₗ[(en : A →+* R)]
      ((ModuleCat.restrictScalars g).obj (ModuleCat.of S S)) :=
    { ej.toAddEquiv with
      map_smul' := fun a b ↦ by
        change ej (f a * (show B from b)) = g (en a) * ej (show B from b)
        rw [map_mul, hs] }
  let e₂ : ((ModuleCat.restrictScalars (en : A →+* R)).obj N) ≃ₛₗ[(en : A →+* R)] N :=
    { AddEquiv.refl _ with map_smul' := fun _ _ ↦ rfl }
  let et := TensorProduct.congr e₁ e₂
  let X := (ModuleCat.extendScalars.{u, u, u + 1} f).obj
    ((ModuleCat.restrictScalars (en : A →+* R)).obj N)
  let Y := (ModuleCat.restrictScalars (ej : B →+* S)).obj
    ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} g).obj N)
  suffices e : X ≃ₗ[B] Y from e.toModuleIso
  refine
    { toFun := fun x ↦ et x
      invFun := fun x ↦ et.symm x
      left_inv := et.left_inv
      right_inv := et.right_inv
      map_add' := fun x y ↦ et.map_add x y
      map_smul' := ?_ }
  intro b x
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul c m =>
    change ej (b * (show B from c)) ⊗ₜ[R, g] m =
      ej b • (ej (show B from c) ⊗ₜ[R, g] m)
    rw [map_mul, TensorProduct.smul_tmul']
    rfl
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- The sections-tensor map is uniquely fixed by its balanced pure-tensor formula.
Source: Bhatt--Scholze 6.8.2(1), blueprint final paragraph
(blueprint: lem-weil-point-sections-scalar-extension).
Proof: send a tensor n to the sheafified tensor of the constant section a with n.
The coefficient maps agree on every finite quotient, so balancing is valid.
The sheaf tensor universal property gives the map. Pure tensors generate its
source, proving uniqueness, and the same formula commutes with every sheaf map.
A finite free basis of R_L over R_E gives a global O_E-basis of O_L by evaluating
at the point; both sides are then the same finite sum of sections. -/
theorem pointSectionsTensor_existsUnique :
    ∃! θ : pointCompletedSections k l E ⋙ pointIntegralModuleTensor l E L ι ≅
        completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k)) ⋙
          pointCompletedSections k l L,
      ∀ (F : integralTowerModules.{u, u} l E (Spec (.of k)))
        (a : Padic.coefficientExtensionIntegers l L)
        (n : (pointCompletedSections k l E).obj F),
        θ.hom.app F (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
          integralScalarIntegerInclusion.{u} l E L ι] n) =
          completedScalarTensorSection.{u, u} l E L ι (Spec (.of k)) F
            (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) (pointCompletedConstant k l L a) n := by
  classical
  let Y := Spec (.of k)
  let U := op (Scheme.ProEt.mk (𝟙 Y))
  let eE := RingEquiv.ofBijective (pointCompletedConstant k l E)
    (pointCompletedConstant_bijective k l E)
  let eL := RingEquiv.ofBijective (pointCompletedConstant k l L)
    (pointCompletedConstant_bijective k l L)
  let φ := completedCoefficientMap l E L ι Y
  let R := completedIntegralCoefficientSheafUnrestricted l L Y
  let i (F : integralTowerModules l E Y) :=
    pointTensorSquareIso (integralScalarIntegerInclusion l E L ι) (φ.hom.app U).hom eE eL
      (fun a ↦ (pointCompletedConstant_compatibility k l E L ι a).symm) (F.val.obj U) ≪≫
    (ModuleCat.restrictScalars eL.toRingHom).mapIso
      (sheafificationFinalIso k R (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ F)) ≪≫
    (pointCompletedSections k l L).mapIso
      (eqToIso (completedOrdinaryScalarExtension_obj l E L ι Y F)).symm
  have hi (F : integralTowerModules l E Y)
      (a : Padic.coefficientExtensionIntegers l L) (n : (pointCompletedSections k l E).obj F) :
      (i F).hom (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
          integralScalarIntegerInclusion l E L ι] n) =
        completedScalarTensorSection l E L ι Y F U (pointCompletedConstant k l L a) n := by
    rfl
  let θ : pointCompletedSections k l E ⋙ pointIntegralModuleTensor l E L ι ≅
      completedOrdinaryScalarExtension l E L ι Y ⋙ pointCompletedSections k l L :=
    NatIso.ofComponents i (by
      intro F G f
      apply ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u}
        (integralScalarIntegerInclusion l E L ι)).homEquiv _ _).injective
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (i G).hom ((1 : Padic.coefficientExtensionIntegers l L)
          ⊗ₜ[_, integralScalarIntegerInclusion l E L ι] (f.val.app U x)) =
        ((completedOrdinaryScalarExtension l E L ι Y).map f).val.app U
          ((i F).hom ((1 : Padic.coefficientExtensionIntegers l L)
            ⊗ₜ[_, integralScalarIntegerInclusion l E L ι] x))
      rw [hi, hi]
      exact (completedScalarTensorSection_naturality l E L ι Y f U _ x).symm)
  refine ⟨θ, hi, ?_⟩
  intro ν hν
  apply Iso.ext
  apply NatTrans.ext
  funext F
  apply ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u}
    (integralScalarIntegerInclusion l E L ι)).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (hν F 1 x).trans (hi F 1 x).symm

/-- The canonical balanced sections-tensor transformation.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointSectionsTensor :=
  (pointSectionsTensor_existsUnique k l E L ι).exists.choose

/-- Finite-free ordinary completed coefficient extension is exact.
Source: Bhatt--Scholze 6.8.2(1)
(blueprint: lem-weil-point-sections-scalar-extension).
Proof: choose a finite free R_E-basis of R_L. Ordinary sheafified tensor is then
naturally a finite direct sum on the underlying R_E-modules. Finite sums are exact,
and restriction of scalars detects exactness. -/
theorem pointCompletedOrdinary_exact :
    PreservesFiniteLimits (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))) ∧
      PreservesFiniteColimits (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))) := by
  exact ⟨podCompletedOrdinaryScalarExtension_preservesFiniteLimits l E L ι (Spec (.of k)),
    podCompletedOrdinaryScalarExtension_preservesFiniteColimits l E L ι (Spec (.of k))⟩

/-- Preservation of kernels by finite-free coefficient extension.
Source: Bhatt--Scholze 6.8.2(1)
(blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCompletedOrdinaryLimits :
    PreservesFiniteLimits (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))) :=
  (pointCompletedOrdinary_exact k l E L ι).1

/-- Preservation of cokernels by coefficient extension.
Source: Bhatt--Scholze 6.8.2(1)
(blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCompletedOrdinaryColimits :
    PreservesFiniteColimits (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))) :=
  (pointCompletedOrdinary_exact k l E L ι).2

/-- The universal derived tensor comparison is the termwise one for a finite-free extension.
Source: Stacks 06YY and Bhatt--Scholze 6.8.2(1)
(blueprint: lem-weil-point-sections-scalar-extension).
Proof: ordinary finite-free tensor preserves every quasi-isomorphism, not only those
between K-flat complexes. Its exact-functor localization is therefore its left derived
functor. The universal counit gives the displayed comparison, and localization at
quasi-isomorphisms makes the normalization on representatives determine it uniquely. -/
theorem pointOrdinaryDerivedComparison_existsUnique :
    ∃! δ : completedDerivedScalarExtension.{u, u} l E L ι (Spec (.of k)) ≅
        (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))).mapDerivedCategory,
      ∀ P : CochainComplex (integralTowerModules.{u, u} l E (Spec (.of k))) ℤ,
        δ.hom.app (DerivedCategory.Q.obj P) ≫
          (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of
        k))).mapDerivedCategoryFactors.hom.app P =
            completedScalarCounit.{u, u} l E L ι (Spec (.of k)) P := by
  obtain ⟨c, hc⟩ := scalar_exact_comparison (l := l) (E := E) (L := L) (ι := ι)
    (Spec (.of k))
  refine ⟨c.symm, hc, ?_⟩
  intro δ hδ
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
  intro P
  exact (cancel_mono
    ((completedOrdinaryScalarExtension l E L ι (Spec (.of k))).mapDerivedCategoryFactors.hom.app
      P)).mp ((hδ P).trans (hc P).symm)

/-- The canonical identification of ordinary derived and termwise tensor.
Source: Stacks 06YY (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointOrdinaryDerivedComparison :=
  (pointOrdinaryDerivedComparison_existsUnique k l E L ι).exists.choose

/-- The derived sections-tensor isomorphism, normalized by actual termwise tensors.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointDerivedSectionsTensor :
    pointCompletedDerivedSections k l E ⋙ pointIntegralModuleDerivedTensor l E L ι ≅
      completedDerivedScalarExtension.{u, u} l E L ι (Spec (.of k)) ⋙
        pointCompletedDerivedSections k l L :=
  (Functor.mapDerivedCategoryCompIso
    (pointCompletedSections k l E) (pointIntegralModuleTensor l E L ι)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pointSectionsTensor k l E L ι) ≪≫
    Functor.mapDerivedCategoryCompIso
      (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k)))
      (pointCompletedSections k l L) ≪≫
    Functor.isoWhiskerRight (pointOrdinaryDerivedComparison k l E L ι).symm
      (pointCompletedDerivedSections k l L)

/-- Multiplication on ordinary sheaf tensor fixes the identity-extension identification.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension).
Proof: multiplication s tensor x to sx is balanced and inverse to x to 1 tensor x.
These formulas commute with restrictions and sheaf maps, and tensors generate,
so they determine exactly one natural isomorphism. -/
theorem pointOrdinaryTensorUnit_existsUnique :
    ∃! μ : completedOrdinaryScalarExtension.{u, u} l E E (AlgHom.id ℚ_[l] E) (Spec (.of k)) ≅
        𝟭 (integralTowerModules.{u, u} l E (Spec (.of k))),
      ∀ (F : integralTowerModules.{u, u} l E (Spec (.of k))) (U : (Spec (.of k)).ProEtᵒᵖ)
        (a : (completedIntegralCoefficientSheafUnrestricted.{u, u} l E (Spec (.of k))).obj.obj U)
        (x : F.val.obj U),
        (μ.hom.app F).val.app U
          (completedScalarTensorSection.{u, u} l E E (AlgHom.id ℚ_[l] E) (Spec (.of k)) F U a x) =
            a • x := by
  classical
  let Y := Spec (.of k)
  let G := completedOrdinaryScalarExtension l E E (AlgHom.id ℚ_[l] E) Y
  let single := CochainComplex.singleFunctor (integralTowerModules.{u, u} l E Y) 0
  let μc := completedScalarIdentityMultiplication l E Y
  let μ : G ≅ 𝟭 _ := NatIso.ofComponents
    (fun F ↦ (HomologicalComplex.eval _ _ (0 : ℤ)).mapIso (μc.app (single.obj F)))
    (by
      intro F F' f
      exact congrArg (fun g ↦ g.f (0 : ℤ)) (μc.hom.naturality (single.map f)))
  have hμ (F : integralTowerModules l E Y) (U : Y.ProEtᵒᵖ)
      (a : (completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U)
      (x : F.val.obj U) :
      (μ.hom.app F).val.app U
        (completedScalarTensorSection l E E (AlgHom.id ℚ_[l] E) Y F U a x) = a • x := by
    exact (completedScalarIdentityMultiplication_existsUnique l E Y).exists.choose_spec
      (single.obj F) 0 U a x
  refine ⟨μ, hμ, ?_⟩
  intro ν hν
  apply Iso.ext
  apply NatTrans.ext
  funext F
  apply (cancel_epi (eqToIso
    (completedOrdinaryScalarExtension_obj l E E (AlgHom.id ℚ_[l] E) Y F)).inv).1
  apply SheafOfModules.tensor_generator_ext
  intro U x a
  exact (hν F U a x).trans (hμ F U a x).symm

/-- The canonical ordinary multiplication isomorphism.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointOrdinaryTensorUnit :=
  (pointOrdinaryTensorUnit_existsUnique k l E).exists.choose

/-- The canonical derived multiplication isomorphism.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointDerivedTensorUnit :
    completedDerivedScalarExtension.{u, u} l E E (AlgHom.id ℚ_[l] E) (Spec (.of k)) ≅
      𝟭 (DerivedCategory (integralTowerModules.{u, u} l E (Spec (.of k)))) :=
  pointOrdinaryDerivedComparison k l E E (AlgHom.id ℚ_[l] E) ≪≫
    Functor.mapDerivedCategoryNatIso (pointOrdinaryTensorUnit k l E) ≪≫
    Functor.mapDerivedCategoryIdIso _

private theorem pointTensorSection_smul_one
    (N : integralTowerModules.{u, u} l E (Spec (.of k)))
    (U : (Spec (.of k)).ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted.{u, u} l L
      (Spec (.of k))).obj.obj U) (x : N.val.obj U) :
    completedScalarTensorSection l E L ι (Spec (.of k)) N U s x =
      s • completedScalarTensorSection l E L ι (Spec (.of k)) N U 1 x := by
  let Y := Spec (.of k)
  have : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{u} _
  let a := completedCoefficientMap.{u, u} l E L ι Y
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (completedIntegralCoefficientSheafUnrestricted l L Y).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a N)
  change (eqToHom (completedOrdinaryScalarExtension_obj l E L ι Y N).symm).val.app U
    (η.app U (s ⊗ₜ[_, (a.hom.app U).hom] x)) =
      s • (eqToHom (completedOrdinaryScalarExtension_obj l E L ι Y N).symm).val.app U
        (η.app U ((1 : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
          ⊗ₜ[_, (a.hom.app U).hom] x))
  rw [← ((eqToHom
    (completedOrdinaryScalarExtension_obj l E L ι Y N).symm).val.app U).hom.map_smul,
    ← (η.app U).hom.map_smul]
  congr 2
  change s ⊗ₜ[_, (a.hom.app U).hom] x = (s * 1) ⊗ₜ[_, (a.hom.app U).hom] x
  rw [mul_one]

private theorem pointScalarAdjunction :
    ∃ A : completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k)) ⊣
        SheafOfModules.SuccessiveDerivedQuotient.restriction.{u + 1, u, u + 1}
          (completedCoefficientMap.{u, u} l E L ι (Spec (.of k))),
      ∀ (N : integralTowerModules.{u, u} l E (Spec (.of k)))
        (U : (Spec (.of k)).ProEtᵒᵖ) (x : N.val.obj U),
        (A.unit.app N).val.app U x =
          completedScalarTensorSection l E L ι (Spec (.of k)) N U 1 x := by
  let Y := Spec (.of k)
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{u} _
  obtain ⟨A, hA⟩ := (SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (completedCoefficientMap.{u, u} l E L ι Y)).2.2
      (completedOrdinaryScalarExtension l E L ι Y)
      (completedOrdinaryScalarExtension_obj l E L ι Y)
      (fun f ↦ completedOrdinaryScalarExtension_map l E L ι Y f)
  refine ⟨A, ?_⟩
  intro N U x
  have h := hA N ((completedOrdinaryScalarExtension l E L ι Y).obj N)
    (eqToHom (completedOrdinaryScalarExtension_obj l E L ι Y N).symm) U x
  simp only [eqToHom_trans, eqToHom_refl, Adjunction.homEquiv_id] at h
  set_option backward.isDefEq.respectTransparency false in
    exact h

private theorem scalarAssocFromUnits
    {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T)
    (hab : a ≫ b = c)
    (F : Modules R ⥤ Modules S) (G : Modules S ⥤ Modules T)
    (H : Modules R ⥤ Modules T)
    (A : F ⊣ restriction a) (B : G ⊣ restriction b) (D : H ⊣ restriction c)
    (sa : ∀ (N : Modules R) U, S.obj.obj U → N.val.obj U → (F.obj N).val.obj U)
    (sb : ∀ (N : Modules S) U, T.obj.obj U → N.val.obj U → (G.obj N).val.obj U)
    (sc : ∀ (N : Modules R) U, T.obj.obj U → N.val.obj U → (H.obj N).val.obj U)
    (ha : ∀ N U x, (A.unit.app N).val.app U x = sa N U 1 x)
    (hb : ∀ N U x, (B.unit.app N).val.app U x = sb N U 1 x)
    (hc : ∀ N U x, (D.unit.app N).val.app U x = sc N U 1 x)
    (hsa : ∀ N U s x, sa N U s x = s • sa N U 1 x)
    (hsb : ∀ N U s x, sb N U s x = s • sb N U 1 x)
    (hsc : ∀ N U s x, sc N U s x = s • sc N U 1 x) :
    ∃! α : F ⋙ G ≅ H, ∀ N U s t x,
      (α.hom.app N).val.app U (sb (F.obj N) U t (sa N U s x)) =
        sc N U (t * b.hom.app U s) x := by
  cases hab
  let adj := (A.comp B).ofNatIsoRight (resComp a b)
  let α := adj.leftAdjointUniq D
  have hu N U x : (α.hom.app N).val.app U (sb (F.obj N) U 1 (sa N U 1 x)) =
      sc N U 1 x := by
    have h := congrArg (fun f ↦ f.val.app U x)
      (Adjunction.unit_leftAdjointUniq_hom_app adj D N)
    change (α.hom.app N).val.app U
      ((B.unit.app _).val.app U ((A.unit.app N).val.app U x)) = _ at h
    rw [ha, hb] at h
    exact h.trans (hc N U x)
  have hα N U s t x :
      (α.hom.app N).val.app U (sb (F.obj N) U t (sa N U s x)) =
        sc N U (t * b.hom.app U s) x := by
    have hs : sb (F.obj N) U 1 (s • sa N U 1 x) =
        b.hom.app U s • sb (F.obj N) U 1 (sa N U 1 x) := by
      have h := ((B.unit.app (F.obj N)).val.app U).hom.map_smul s (sa N U 1 x)
      change (B.unit.app (F.obj N)).val.app U (s • sa N U 1 x) =
        b.hom.app U s • (show (G.obj (F.obj N)).val.obj U from
          (B.unit.app (F.obj N)).val.app U (sa N U 1 x)) at h
      rw [hb, hb] at h
      exact h
    rw [hsa, hsb, hs, ((α.hom.app N).val.app U).hom.map_smul,
      ((α.hom.app N).val.app U).hom.map_smul, hu, hsc N U (t * b.hom.app U s) x]
    exact smul_smul t (b.hom.app U s) (sc N U 1 x)
  refine ⟨α, hα, ?_⟩
  intro β hβ
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply ((A.comp B).homEquiv N _).injective
  ext U x
  change (β.hom.app N).val.app U
    ((B.unit.app _).val.app U ((A.unit.app N).val.app U x)) =
    (α.hom.app N).val.app U
      ((B.unit.app _).val.app U ((A.unit.app N).val.app U x))
  rw [ha, hb]
  exact (hβ N U 1 1 x).trans (hα N U 1 1 x).symm

private theorem pointCompletedCoefficientMap_comp :
    completedCoefficientMap.{u, u} l E M (κ.comp ι) (Spec (.of k)) =
      completedCoefficientMap.{u, u} l E L ι (Spec (.of k)) ≫
        completedCoefficientMap.{u, u} l L M κ (Spec (.of k)) := by
  let Y := Spec (.of k)
  apply (completedCoefficientMap_existsUnique l E M (κ.comp ι) Y).unique
  · exact (completedCoefficientMap_existsUnique l E M (κ.comp ι) Y).exists.choose_spec
  · intro n
    rw [Category.assoc, completedCoefficientMap_projection, ← Category.assoc,
      completedCoefficientMap_projection, Category.assoc]
    congr 1
    have hq : integralScalarQuotientMap l E M (κ.comp ι) n =
        (integralScalarQuotientMap l L M κ n).comp
          (integralScalarQuotientMap l E L ι n) := by
      apply RingHom.ext
      intro x
      induction x using Quotient.inductionOn' with
      | h x => rfl
    unfold integralScalarQuotientSheafMap
    rw [← Functor.map_comp, hq]
    congr 1

/-- The balanced sheaf-tensor associator is fixed on all iterated pure tensors.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension).
Proof: send b tensor (a tensor x) to b*iota(a) tensor x. Balancing proves that
this is well defined; its inverse sends c tensor x to c tensor (1 tensor x).
The two composites are identities on generators. These maps respect restrictions
and all sheaf morphisms, and their generator formulas imply uniqueness. -/
theorem pointOrdinaryTensorAssoc_existsUnique :
    ∃! α : completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k)) ⋙
        completedOrdinaryScalarExtension.{u, u} l L M κ (Spec (.of k)) ≅
        completedOrdinaryScalarExtension.{u, u} l E M (κ.comp ι) (Spec (.of k)),
      ∀ (F : integralTowerModules.{u, u} l E (Spec (.of k))) (U : (Spec (.of k)).ProEtᵒᵖ)
        (a : (completedIntegralCommRingSheafUnrestricted.{u, u} l L (Spec (.of k))).obj.obj U)
        (b : (completedIntegralCommRingSheafUnrestricted.{u, u} l M (Spec (.of k))).obj.obj U)
        (x : F.val.obj U),
        (α.hom.app F).val.app U
          (completedScalarTensorSection.{u, u} l L M κ (Spec (.of k))
            ((completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))).obj F) U b
            (completedScalarTensorSection.{u, u} l E L ι (Spec (.of k)) F U a x)) =
          completedScalarTensorSection.{u, u} l E M (κ.comp ι) (Spec (.of k)) F U
            (b * (completedCoefficientMap.{u, u} l L M κ (Spec (.of k))).hom.app U a) x := by
  let : EssentiallySmall.{u + 1} (Spec (.of k)).ProEt := essentiallySmallSelf.{u} _
  obtain ⟨A, hA⟩ := pointScalarAdjunction k l E L ι
  obtain ⟨B, hB⟩ := pointScalarAdjunction k l L M κ
  obtain ⟨C, hC⟩ := pointScalarAdjunction k l E M (κ.comp ι)
  exact scalarAssocFromUnits _ _ _
    (pointCompletedCoefficientMap_comp k l E L ι M κ).symm _ _ _ A B C
    (completedScalarTensorSection l E L ι (Spec (.of k)))
    (completedScalarTensorSection l L M κ (Spec (.of k)))
    (completedScalarTensorSection l E M (κ.comp ι) (Spec (.of k))) hA hB hC
    (pointTensorSection_smul_one k l E L ι)
    (pointTensorSection_smul_one k l L M κ)
    (pointTensorSection_smul_one k l E M (κ.comp ι))

/-- The canonical ordinary tensor associator.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointOrdinaryTensorAssoc :=
  (pointOrdinaryTensorAssoc_existsUnique k l E L ι M κ).exists.choose

/-- The ordinary derived tensor associator, descended from the balanced maps.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointDerivedTensorAssoc :
    completedDerivedScalarExtension.{u, u} l E L ι (Spec (.of k)) ⋙
      completedDerivedScalarExtension.{u, u} l L M κ (Spec (.of k)) ≅
      completedDerivedScalarExtension.{u, u} l E M (κ.comp ι) (Spec (.of k)) :=
  Functor.isoWhiskerRight (pointOrdinaryDerivedComparison k l E L ι) _ ≪≫
    Functor.isoWhiskerLeft _ (pointOrdinaryDerivedComparison k l L M κ) ≪≫
    (Functor.mapDerivedCategoryCompIso
      (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k)))
      (completedOrdinaryScalarExtension.{u, u} l L M κ (Spec (.of k)))).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pointOrdinaryTensorAssoc k l E L ι M κ) ≪≫
    (pointOrdinaryDerivedComparison k l E M (κ.comp ι)).symm

private theorem scalarTransport_tmul {R S : Type u} [CommRing R] [CommRing S]
    (f g : R →+* S) (h : f = g) (P : ModuleCat.{max u v} R) (s : S) (n : P) :
    (eqToIso (congrArg (ModuleCat.extendScalars.{u, u, max u v}) h)).hom.app P
      (s ⊗ₜ[R, f] n) = s ⊗ₜ[R, g] n := by
  subst g
  rfl

/-- The module associator is the ordinary balanced multiplication of coefficient factors.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension).
Proof: send b tensor (a tensor n) to b*kappa(a) tensor n, with inverse c tensor n
to c tensor (1 tensor n). Balancing proves the inverse identities and naturality;
generators determine the map uniquely. -/
theorem pointIntegralModuleAssoc_existsUnique :
    ∃! α : pointIntegralModuleTensor l E L ι ⋙ pointIntegralModuleTensor l L M κ ≅
        pointIntegralModuleTensor l E M (κ.comp ι),
      ∀ (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
        (a : Padic.coefficientExtensionIntegers l L)
        (b : Padic.coefficientExtensionIntegers l M) (n : N),
        α.hom.app N
          (b ⊗ₜ[Padic.coefficientExtensionIntegers l L,
            integralScalarIntegerInclusion.{u} l L M κ]
            (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
              integralScalarIntegerInclusion.{u} l E L ι] n)) =
          (b * integralScalarIntegerInclusion.{u} l L M κ a) ⊗ₜ[
            Padic.coefficientExtensionIntegers l E,
            integralScalarIntegerInclusion.{u} l E M (κ.comp ι)] n := by
  let α := coefficientComplexIntegralAssoc.{u, u + 1} l E L ι M κ
  have hα (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
      (a : Padic.coefficientExtensionIntegers l L)
      (b : Padic.coefficientExtensionIntegers l M) (n : N) :
      α.hom.app N (b ⊗ₜ[Padic.coefficientExtensionIntegers l L,
        integralScalarIntegerInclusion l L M κ]
        (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
          integralScalarIntegerInclusion l E L ι] n)) =
        (b * integralScalarIntegerInclusion l L M κ a) ⊗ₜ[
          Padic.coefficientExtensionIntegers l E,
          integralScalarIntegerInclusion l E M (κ.comp ι)] n := by
    dsimp only [α, coefficientComplexIntegralAssoc, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app]
    rw [ModuleCat.comp_apply, scalarComp_inv_tmul.{u, u + 1},
      scalarTransport_tmul.{u, u + 1} _ _ (coefficientComplexIntegerComp l E L ι M κ)]
  refine ⟨α, hα, ?_⟩
  intro β hβ
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply scalarDouble_hom_ext.{u, u + 1}
    (integralScalarIntegerInclusion l E L ι) (integralScalarIntegerInclusion l L M κ)
  intro n
  exact (hβ N 1 1 n).trans (hα N 1 1 n).symm

/-- The ordinary module-complex associator in the derived category.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointIntegralModuleDerivedAssoc :
    pointIntegralModuleDerivedTensor l E L ι ⋙ pointIntegralModuleDerivedTensor l L M κ ≅
      pointIntegralModuleDerivedTensor l E M (κ.comp ι) :=
  (Functor.mapDerivedCategoryCompIso
    (pointIntegralModuleTensor l E L ι) (pointIntegralModuleTensor l L M κ)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (pointIntegralModuleAssoc_existsUnique l E L ι M κ).exists.choose

set_option backward.isDefEq.respectTransparency.types false in
omit [IsAlgClosed k] in
attribute [local irreducible] completedScalarChangeData
  completedIntegralCoefficientSheafUnrestricted

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
omit [IsAlgClosed k] in
section AbstractAssociator

universe v w r
variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]

open SheafOfModules.SuccessiveDerivedQuotient in
end AbstractAssociator

variable (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (κ : L →ₐ[ℚ_[l]] M)

omit [IsAlgClosed k] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Fraction-field extension on coefficient modules.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable abbrev pointModuleRationalization :=
  ModuleCat.extendScalars.{u, u, u + 1}
    (algebraMap (Padic.coefficientExtensionIntegers l E) E)

/-- Additivity of localization to the coefficient field.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointModuleRationalizationAdditive :
    (pointModuleRationalization l E).Additive :=
  (pointCoefficientTensors_exact l E E (AlgHom.id ℚ_[l] E)).2.1

/-- Localization preserves kernels.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointModuleRationalizationLimits :
    PreservesFiniteLimits (pointModuleRationalization l E) :=
  (pointCoefficientTensors_exact l E E (AlgHom.id ℚ_[l] E)).2.2.1

/-- Localization preserves cokernels.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointModuleRationalizationColimits :
    PreservesFiniteColimits (pointModuleRationalization l E) :=
  (pointCoefficientTensors_exact l E E (AlgHom.id ℚ_[l] E)).2.2.2

/-- Ordinary termwise tensor with the fraction field on derived modules.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable abbrev pointModuleDerivedRationalization :=
  (pointModuleRationalization l E).mapDerivedCategory

/-- Tensor with a coefficient field extension is exact and additive.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension).
Proof: a field extension is a free module, so tensor is a direct sum of copies on
underlying vector spaces and preserves kernels and cokernels. It adds maps termwise. -/
theorem pointCoefficientFieldTensor_exact :
    (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom).Additive ∧
      PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom) ∧
      PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom) := by
  exact (coefficientComplexTensors_exact.{u, u + 1} l E L ι).2.2.2

/-- Additivity of coefficient field extension.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCoefficientFieldTensorAdditive :
    (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom).Additive :=
  (pointCoefficientFieldTensor_exact l E L ι).1

/-- Coefficient field extension preserves kernels.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCoefficientFieldTensorLimits :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom) :=
  (pointCoefficientFieldTensor_exact l E L ι).2.1

/-- Coefficient field extension preserves cokernels.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCoefficientFieldTensorColimits :
    PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom) :=
  (pointCoefficientFieldTensor_exact l E L ι).2.2

/-- Termwise coefficient field extension on derived vector spaces.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable abbrev pointCoefficientFieldDerivedTensor :=
  (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom).mapDerivedCategory

/-- The ordinary field-complex associator.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointCoefficientFieldDerivedAssoc :
    pointCoefficientFieldDerivedTensor l E L ι ⋙ pointCoefficientFieldDerivedTensor l L M κ ≅
      pointCoefficientFieldDerivedTensor l E M (κ.comp ι) :=
  (Functor.mapDerivedCategoryCompIso
    (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom) (ModuleCat.extendScalars.{u, u, u + 1}
        κ.toRingHom)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (ModuleCat.extendScalarsComp.{u, u + 1} ι.toRingHom
        κ.toRingHom).symm

/-- Rationalization and finite extension commute by the actual balanced localization map.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension).
Proof: send b tensor (a tensor n) to ba tensor (1 tensor n), where a is included
in L. The inverse sends b tensor (x tensor n) to b*iota(x) tensor (1 tensor n).
All nonzero O_E-elements are units in L, so denominators move across the tensor
relation. These maps respect the balanced relations and are mutual inverses;
their formulas commute with module morphisms and determine the map uniquely. -/
theorem pointTensorRationalization_existsUnique :
    ∃! β : pointIntegralModuleTensor l E L ι ⋙ pointModuleRationalization l L ≅
        pointModuleRationalization l E ⋙ ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom,
      ∀ (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
        (a : Padic.coefficientExtensionIntegers l L) (b : L) (n : N),
        β.hom.app N
          (b ⊗ₜ[Padic.coefficientExtensionIntegers l L,
            algebraMap (Padic.coefficientExtensionIntegers l L) L]
            (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
              integralScalarIntegerInclusion.{u} l E L ι] n)) =
          (b * (a : L)) ⊗ₜ[E, ι.toRingHom]
            ((1 : E) ⊗ₜ[Padic.coefficientExtensionIntegers l E,
              algebraMap (Padic.coefficientExtensionIntegers l E) E] n) := by
  exact coefficientComplexBeta_existsUnique.{u, u + 1} l E L ι

/-- The canonical localization-tensor associator on module derived categories.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointDerivedTensorRationalization :
    pointIntegralModuleDerivedTensor l E L ι ⋙ pointModuleDerivedRationalization l L ≅
      pointModuleDerivedRationalization l E ⋙ pointCoefficientFieldDerivedTensor l E L ι :=
  (Functor.mapDerivedCategoryCompIso
    (pointIntegralModuleTensor l E L ι) (pointModuleRationalization l L)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (pointTensorRationalization_existsUnique l E L ι).exists.choose ≪≫
      Functor.mapDerivedCategoryCompIso
        (pointModuleRationalization l E) (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom)

private theorem ordinarySectionsTowerTransport
    {C₀ : Type a} {C₁ : Type b} {C₂ : Type c}
    {D₀ : Type d} {D₁ : Type e} {D₂ : Type f}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    (S₀ : C₀ ⥤ D₀) (S₁ : C₁ ⥤ D₁) (S₂ : C₂ ⥤ D₂)
    (M₁ : D₀ ⥤ D₁) (M₂ : D₁ ⥤ D₂) (M₃ : D₀ ⥤ D₂)
    (t₁ : S₀ ⋙ M₁ ≅ F ⋙ S₁) (t₂ : S₁ ⋙ M₂ ≅ G ⋙ S₂)
    (t₃ : S₀ ⋙ M₃ ≅ H ⋙ S₂) (a : F ⋙ G ≅ H) (m : M₁ ⋙ M₂ ≅ M₃)
    (h : ∀ K, M₂.map (t₁.hom.app K) ≫ t₂.hom.app (F.obj K) ≫
      S₂.map (a.hom.app K) = m.hom.app (S₀.obj K) ≫ t₃.hom.app K) :
    Functor.isoWhiskerRight a S₂ ≪≫ t₃.symm =
      Functor.isoWhiskerLeft F t₂.symm ≪≫ Functor.isoWhiskerRight t₁.symm M₂ ≪≫
        Functor.isoWhiskerLeft S₀ m := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply (cancel_epi (M₂.map (t₁.hom.app K) ≫ t₂.hom.app (F.obj K))).mp
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.assoc,
    Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  have hf := congrArg (fun z ↦ z ≫ t₃.inv.app K) (h K)
  simp only [Category.assoc, Iso.hom_inv_id_app] at hf
  exact hf.trans (Category.comp_id _)

private theorem transportTower
    {C₀ : Type a} {C₁ : Type b} {C₂ : Type c}
    {D₀ : Type d} {D₁ : Type e} {D₂ : Type f}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (T₁ F₁ : C₀ ⥤ C₁) (T₂ F₂ : C₁ ⥤ C₂) (T₃ F₃ : C₀ ⥤ C₂)
    (S₀ : C₀ ⥤ D₀) (S₁ : C₁ ⥤ D₁) (S₂ : C₂ ⥤ D₂)
    (M₁ : D₀ ⥤ D₁) (M₂ : D₁ ⥤ D₂) (M₃ : D₀ ⥤ D₂)
    (d₁ : T₁ ≅ F₁) (d₂ : T₂ ≅ F₂) (d₃ : T₃ ≅ F₃)
    (t₁ : S₀ ⋙ M₁ ≅ F₁ ⋙ S₁) (t₂ : S₁ ⋙ M₂ ≅ F₂ ⋙ S₂)
    (t₃ : S₀ ⋙ M₃ ≅ F₃ ⋙ S₂) (a : F₁ ⋙ F₂ ≅ F₃)
    (m : M₁ ⋙ M₂ ≅ M₃) (K : C₀)
    (h : S₂.map (a.hom.app K) ≫ t₃.inv.app K =
      t₂.inv.app (F₁.obj K) ≫ M₂.map (t₁.inv.app K) ≫ m.hom.app (S₀.obj K)) :
    S₂.map ((T₂.map (d₁.hom.app K)) ≫ d₂.hom.app (F₁.obj K) ≫
        a.hom.app K ≫ d₃.inv.app K) ≫ S₂.map (d₃.hom.app K) ≫ t₃.inv.app K =
      S₂.map (d₂.hom.app (T₁.obj K)) ≫ t₂.inv.app (T₁.obj K) ≫
        M₂.map (S₁.map (d₁.hom.app K) ≫ t₁.inv.app K) ≫
        m.hom.app (S₀.obj K) := by
  simp only [Functor.map_comp, Category.assoc]
  have hc : S₂.map (d₃.inv.app K) ≫ S₂.map (d₃.hom.app K) = 𝟙 _ := by
    rw [← S₂.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rw [reassoc_of% hc]
  rw [h]
  have hd := congrArg S₂.map (d₂.hom.naturality (d₁.hom.app K))
  simp only [Functor.map_comp] at hd
  rw [reassoc_of% hd]
  have ht := t₂.inv.naturality (d₁.hom.app K)
  simp only [Functor.comp_map] at ht
  rw [reassoc_of% ht]

private theorem pointOrdinarySectionsTowerForward
    (N : integralTowerModules.{u, u} l E (Spec (.of k))) :
    (pointIntegralModuleTensor l L M κ).map
        ((pointSectionsTensor k l E L ι).hom.app N) ≫
      (pointSectionsTensor k l L M κ).hom.app
        ((completedOrdinaryScalarExtension l E L ι (Spec (.of k))).obj N) ≫
      (pointCompletedSections k l M).map
        ((pointOrdinaryTensorAssoc k l E L ι M κ).hom.app N) =
    (pointIntegralModuleAssoc_existsUnique l E L ι M κ).exists.choose.hom.app
        ((pointCompletedSections k l E).obj N) ≫
      (pointSectionsTensor k l E M (κ.comp ι)).hom.app N := by
  apply scalarDouble_hom_ext.{u, u + 1}
    (integralScalarIntegerInclusion l E L ι)
    (integralScalarIntegerInclusion l L M κ)
  intro x
  simp only [ModuleCat.comp_apply]
  change ((pointOrdinaryTensorAssoc k l E L ι M κ).hom.app N).val.app
    (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))
    ((pointSectionsTensor k l L M κ).hom.app _
      ((1 : Padic.coefficientExtensionIntegers l M) ⊗ₜ[_,
        integralScalarIntegerInclusion l L M κ]
        ((pointSectionsTensor k l E L ι).hom.app N
          ((1 : Padic.coefficientExtensionIntegers l L) ⊗ₜ[_,
            integralScalarIntegerInclusion l E L ι] x)))) = _
  erw [(pointSectionsTensor_existsUnique k l E L ι).exists.choose_spec]
  erw [(pointSectionsTensor_existsUnique k l L M κ).exists.choose_spec]
  erw [(pointOrdinaryTensorAssoc_existsUnique k l E L ι M κ).exists.choose_spec]
  erw [(pointIntegralModuleAssoc_existsUnique l E L ι M κ).exists.choose_spec]
  erw [(pointSectionsTensor_existsUnique k l E M (κ.comp ι)).exists.choose_spec]
  simp only [map_one, mul_one]

private theorem pointOrdinarySectionsTower :
    Functor.isoWhiskerRight (pointOrdinaryTensorAssoc k l E L ι M κ)
        (pointCompletedSections k l M) ≪≫
      (pointSectionsTensor k l E M (κ.comp ι)).symm =
    Functor.isoWhiskerLeft
        (completedOrdinaryScalarExtension l E L ι (Spec (.of k)))
        (pointSectionsTensor k l L M κ).symm ≪≫
      Functor.isoWhiskerRight (pointSectionsTensor k l E L ι).symm
        (pointIntegralModuleTensor l L M κ) ≪≫
      Functor.isoWhiskerLeft (pointCompletedSections k l E)
        (pointIntegralModuleAssoc_existsUnique l E L ι M κ).exists.choose := by
  exact ordinarySectionsTowerTransport
    (completedOrdinaryScalarExtension l E L ι (Spec (.of k)))
    (completedOrdinaryScalarExtension l L M κ (Spec (.of k)))
    (completedOrdinaryScalarExtension l E M (κ.comp ι) (Spec (.of k)))
    (pointCompletedSections k l E) (pointCompletedSections k l L)
    (pointCompletedSections k l M)
    (pointIntegralModuleTensor l E L ι) (pointIntegralModuleTensor l L M κ)
    (pointIntegralModuleTensor l E M (κ.comp ι))
    (pointSectionsTensor k l E L ι) (pointSectionsTensor k l L M κ)
    (pointSectionsTensor k l E M (κ.comp ι))
    (pointOrdinaryTensorAssoc k l E L ι M κ)
    (pointIntegralModuleAssoc_existsUnique l E L ι M κ).exists.choose
    (pointOrdinarySectionsTowerForward k l E L ι M κ)

private theorem pointDerivedSectionsTower
    (K : DerivedCategory (integralTowerModules.{u, u} l E (Spec (.of k)))) :
    (pointCompletedDerivedSections k l M).map
        ((pointDerivedTensorAssoc k l E L ι M κ).hom.app K) ≫
      (pointDerivedSectionsTensor k l E M (κ.comp ι)).inv.app K =
    (pointDerivedSectionsTensor k l L M κ).inv.app
        ((completedDerivedScalarExtension l E L ι (Spec (.of k))).obj K) ≫
      (pointIntegralModuleDerivedTensor l L M κ).map
        ((pointDerivedSectionsTensor k l E L ι).inv.app K) ≫
      (pointIntegralModuleDerivedAssoc l E L ι M κ).hom.app
        ((pointCompletedDerivedSections k l E).obj K) := by
  have h := deriveCoefficientTower
    (completedOrdinaryScalarExtension l E L ι (Spec (.of k)))
    (completedOrdinaryScalarExtension l L M κ (Spec (.of k)))
    (pointCompletedSections k l M) (pointCompletedSections k l E)
    (pointCompletedSections k l L) (pointIntegralModuleTensor l E L ι)
    (pointIntegralModuleTensor l L M κ)
    (completedOrdinaryScalarExtension l E M (κ.comp ι) (Spec (.of k)))
    (pointIntegralModuleTensor l E M (κ.comp ι))
    (pointOrdinaryTensorAssoc k l E L ι M κ)
    (pointSectionsTensor k l E M (κ.comp ι)).symm
    (pointSectionsTensor k l L M κ).symm
    (pointSectionsTensor k l E L ι).symm
    (pointIntegralModuleAssoc_existsUnique l E L ι M κ).exists.choose
    (pointOrdinarySectionsTower k l E L ι M κ) K
  let T₁ := completedOrdinaryScalarExtension l E L ι (Spec (.of k))
  let T₂ := completedOrdinaryScalarExtension l L M κ (Spec (.of k))
  let T₃ := completedOrdinaryScalarExtension l E M (κ.comp ι) (Spec (.of k))
  let a := (Functor.mapDerivedCategoryCompIso T₁ T₂).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pointOrdinaryTensorAssoc k l E L ι M κ)
  let t₁ := Functor.mapDerivedCategorySquareIso (pointSectionsTensor k l E L ι)
  let t₂ := Functor.mapDerivedCategorySquareIso (pointSectionsTensor k l L M κ)
  let t₃ := Functor.mapDerivedCategorySquareIso (pointSectionsTensor k l E M (κ.comp ι))
  have h' : (pointCompletedDerivedSections k l M).map (a.hom.app K) ≫ t₃.inv.app K =
      t₂.inv.app (T₁.mapDerivedCategory.obj K) ≫
        (pointIntegralModuleDerivedTensor l L M κ).map (t₁.inv.app K) ≫
        (pointIntegralModuleDerivedAssoc l E L ι M κ).hom.app
          ((pointCompletedDerivedSections k l E).obj K) := by
    simpa only [a, t₁, t₂, t₃, T₁, T₂,
      pointIntegralModuleDerivedAssoc, Functor.mapDerivedCategorySquareIso,
      Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
      Functor.mapDerivedCategoryNatIso_symm, NatTrans.comp_app, Category.assoc] using h
  have ht := transportTower
    (completedDerivedScalarExtension l E L ι (Spec (.of k))) T₁.mapDerivedCategory
    (completedDerivedScalarExtension l L M κ (Spec (.of k))) T₂.mapDerivedCategory
    (completedDerivedScalarExtension l E M (κ.comp ι) (Spec (.of k))) T₃.mapDerivedCategory
    (pointCompletedDerivedSections k l E) (pointCompletedDerivedSections k l L)
    (pointCompletedDerivedSections k l M)
    (pointIntegralModuleDerivedTensor l E L ι) (pointIntegralModuleDerivedTensor l L M κ)
    (pointIntegralModuleDerivedTensor l E M (κ.comp ι))
    (pointOrdinaryDerivedComparison k l E L ι) (pointOrdinaryDerivedComparison k l L M κ)
    (pointOrdinaryDerivedComparison k l E M (κ.comp ι))
    t₁ t₂ t₃ a (pointIntegralModuleDerivedAssoc l E L ι M κ) K h'
  simpa only [pointDerivedSectionsTensor, pointDerivedTensorAssoc,
    a, t₁, t₂, t₃, T₁, T₂, T₃,
    Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Iso.app_hom, Iso.app_inv, Category.assoc] using ht

private theorem pointModuleAssoc_eq :
    (pointIntegralModuleAssoc_existsUnique l E L ι M κ).exists.choose =
      coefficientComplexIntegralAssoc.{u, u + 1} l E L ι M κ := by
  apply (pointIntegralModuleAssoc_existsUnique l E L ι M κ).unique
  · exact (pointIntegralModuleAssoc_existsUnique l E L ι M κ).exists.choose_spec
  · intro N a b n
    dsimp only [coefficientComplexIntegralAssoc, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app]
    rw [ModuleCat.comp_apply, scalarComp_inv_tmul.{u, u + 1},
      scalarTransport_tmul.{u, u + 1} _ _ (coefficientComplexIntegerComp l E L ι M κ)]

/-- The comparison selected by its unique generator formula.
Source: blueprint coefficient-point paragraph; Stacks 00CX
(blueprint: lem-weil-coefficient-complex-rationalization). -/
private noncomputable def coefficientComplexBeta :=
  (coefficientComplexBeta_existsUnique.{u, v} l E L ι).exists.choose

private theorem pointModuleBeta_eq :
    (pointTensorRationalization_existsUnique l E L ι).exists.choose =
      coefficientComplexBeta.{u, u + 1} l E L ι := by
  apply (pointTensorRationalization_existsUnique l E L ι).unique
  · exact (pointTensorRationalization_existsUnique l E L ι).exists.choose_spec
  · exact (coefficientComplexBeta_existsUnique.{u, u + 1} l E L ι).exists.choose_spec

/-- The field associator, multiplying the two scalar factors.
Source: blueprint coefficient-point paragraph; Stacks 00CX
(blueprint: lem-weil-coefficient-complex-rationalization). -/
private noncomputable def coefficientComplexFieldAssoc :
    coefficientComplexFieldTensor.{u, v} l E L ι ⋙
      coefficientComplexFieldTensor.{u, v} l L M κ ≅
    coefficientComplexFieldTensor.{u, v} l E M (κ.comp ι) :=
  (ModuleCat.extendScalarsComp ι.toRingHom κ.toRingHom).symm

private theorem coefficientBeta_formula
    (P : ModuleCat.{max u v} (Padic.coefficientExtensionIntegers l E))
    (a : Padic.coefficientExtensionIntegers l L) (b : L) (n : P) :
    (coefficientComplexBeta.{u, v} l E L ι).hom.app P
      (b ⊗ₜ[Padic.coefficientExtensionIntegers l L,
        (Padic.coefficientExtensionIntegers l L).subtype]
        (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
          integralScalarIntegerInclusion l E L ι] n)) =
      (b * (a : L)) ⊗ₜ[E, ι.toRingHom]
        ((1 : E) ⊗ₜ[Padic.coefficientExtensionIntegers l E,
          (Padic.coefficientExtensionIntegers l E).subtype] n) :=
  (coefficientComplexBeta_existsUnique.{u, v} l E L ι).exists.choose_spec P a b n

private theorem coefficientModuleTower
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
    (κ : L →ₐ[Padic l] M)
    (P : ModuleCat.{max u v} (Padic.coefficientExtensionIntegers l E)) :
    (coefficientComplexRationalize.{u, v} l M).map
      ((coefficientComplexIntegralAssoc.{u, v} l E L ι M κ).hom.app P) ≫
      (coefficientComplexBeta.{u, v} l E M (κ.comp ι)).hom.app P =
    (coefficientComplexBeta.{u, v} l L M κ).hom.app
        ((coefficientComplexIntegralTensor.{u, v} l E L ι).obj P) ≫
      (coefficientComplexFieldTensor.{u, v} l L M κ).map
        ((coefficientComplexBeta.{u, v} l E L ι).hom.app P) ≫
      (coefficientComplexFieldAssoc.{u, v} l E L ι M κ).hom.app
        ((coefficientComplexRationalize.{u, v} l E).obj P) := by
  apply scalarTriple_hom_ext
  intro n
  simp only [ModuleCat.comp_apply]
  change (coefficientComplexBeta.{u, v} l E M (κ.comp ι)).hom.app P
      ((1 : M) ⊗ₜ[Padic.coefficientExtensionIntegers l M,
        (Padic.coefficientExtensionIntegers l M).subtype]
        ((ModuleCat.extendScalarsComp (integralScalarIntegerInclusion l E L ι)
          (integralScalarIntegerInclusion l L M κ)).inv.app P
          ((1 : Padic.coefficientExtensionIntegers l M) ⊗ₜ[
            Padic.coefficientExtensionIntegers l L, integralScalarIntegerInclusion l L M κ]
            ((1 : Padic.coefficientExtensionIntegers l L) ⊗ₜ[
              Padic.coefficientExtensionIntegers l E,
              integralScalarIntegerInclusion l E L ι] n)))) = _
  erw [scalarComp_inv_tmul]
  simp only [map_one, mul_one]
  erw [coefficientBeta_formula, coefficientBeta_formula]
  simp only [Subring.coe_one, mul_one]
  erw [ModuleCat.ExtendScalars.map_tmul, coefficientBeta_formula]
  simp only [Subring.coe_one, mul_one, coefficientComplexFieldAssoc, Iso.symm_hom]
  erw [scalarComp_inv_tmul]
  simp only [map_one, mul_one]

private theorem pointRationalizationTower
    (K : DerivedCategory (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))) :
    (pointModuleDerivedRationalization l M).map
        ((pointIntegralModuleDerivedAssoc l E L ι M κ).hom.app K) ≫
      (pointDerivedTensorRationalization l E M (κ.comp ι)).hom.app K =
    (pointDerivedTensorRationalization l L M κ).hom.app
        ((pointIntegralModuleDerivedTensor l E L ι).obj K) ≫
      (pointCoefficientFieldDerivedTensor l L M κ).map
        ((pointDerivedTensorRationalization l E L ι).hom.app K) ≫
      (pointCoefficientFieldDerivedAssoc l E L ι M κ).hom.app
        ((pointModuleDerivedRationalization l E).obj K) := by
  apply deriveCoefficientTower
  apply Iso.ext
  apply NatTrans.ext
  funext P
  simp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  rw [pointModuleAssoc_eq, pointModuleBeta_eq, pointModuleBeta_eq, pointModuleBeta_eq]
  exact coefficientModuleTower.{u, u + 1} l E L ι M κ P

set_option backward.isDefEq.respectTransparency true

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
section Constructible

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- The algebraic closure in the fixed finite-field datum is algebraically closed.
Source: blueprint finite-field conventions
(blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointDatumIsAlgClosed : IsAlgClosed D.k :=
  IsAlgClosure.isAlgClosed D.k₀

/-- The two recorded constructibility interfaces describe the same point objects.
Source: blueprint order 1459 and the point's fixed finite-field datum
(blueprint: lem-weil-point-sections-scalar-extension).
Proof: both predicates require derived completeness of the same completed coefficient
module complex. Identify their quotient reductions by the normalized change-of-rings
counit on K-flat representatives. These identifications preserve constructibility
and cohomological support. The support inclusion in Icc is exactly the pair of bounds
in the finite-field interface, with the same interval for every positive exponent. -/
theorem pointIntegralConstructible_iff
    (K : completedIntegralDerivedCategory l E (Spec (.of D.k)) D hl) :
    boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k)) K ↔
      sfIntegralConstructible l E (Spec (.of D.k)) K := by
  exact (constructible_iff_legacy l E (Spec (.of D.k)) D hl K).symm

/-- The canonical completion comparison is invertible on the constructible integral category.
Source: Bhatt--Scholze 3.4.12 and blueprint final paragraph
(blueprint: lem-weil-point-sections-scalar-extension).
Proof: the defining constructible predicate includes derived completeness. Its
augmented reduction tower is the same strict tower as the unrestricted predicate:
both units send x to 1 tensor x, and their product and cone maps agree. Apply
lem-weil-finite-free-completed-scalar-comparison to this complete object. -/
theorem pointConstructibleCompletionComparison_isIso
    (K : completedIntegralDerivedCategory l E
            (Spec (.of D.k)) D hl)
    (_hK : boundedConstructibleDerivedCompleteIntegral D l hl E
            (Spec (.of D.k)) K) :
    IsIso ((completedScalarComparison.{u, u} l E L ι
            (Spec (.of D.k))).app K) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
    let D₀ := scalarExtensionDatum.{0} p hprime
    have hl₀ : l ≠ D₀.p := by
      change l ≠ p
      omega
    have hcomplete : IsDerivedCompleteUnrestricted l E (Spec (.of D.k)) K := by
      refine ⟨D₀, hl₀, ?_⟩
      exact (sfDerivedComplete_iff_legacy l E (Spec (.of D.k)) D₀ hl₀ K).mp
        ((pointIntegralConstructible_iff l E D hl K).mp _hK).1
    exact ((finiteFreeCompletedScalarComparison l E L ι (Spec (.of D.k))).2.1
      K hcomplete).1

set_option backward.isDefEq.respectTransparency false in
/-- The actual completion comparison as an isomorphism on an integral constructible object.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointConstructibleCompletionIso
    (K : completedIntegralDerivedCategory l E
            (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E
            (Spec (.of D.k)) K) :
    (completedDerivedScalarExtension.{u, u} l E L ι
            (Spec (.of D.k))).obj K ≅
      (integralScalarExtension.{u} l E L ι
            (Spec (.of D.k))).obj K :=
  letI := pointConstructibleCompletionComparison_isIso l E L ι D hl K hK
  asIso ((completedScalarComparison.{u, u} l E L ι
            (Spec (.of D.k))).app K)

/-- Phi is precisely the inverse of sections of chi after the canonical sections-tensor map.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointSectionsScalarExtensionIso
    (K : completedIntegralDerivedCategory l E
            (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E
            (Spec (.of D.k)) K) :
    (pointCompletedDerivedSections D.k l L).obj
        ((integralScalarExtension.{u} l E L ι
            (Spec (.of D.k))).obj K) ≅
      (pointIntegralModuleDerivedTensor l E L ι).obj
        ((pointCompletedDerivedSections D.k l E).obj K) :=
  ((pointDerivedSectionsTensor D.k l E L ι).app K ≪≫
    (pointCompletedDerivedSections D.k l L).mapIso
      (pointConstructibleCompletionIso l E L ι D hl K hK)).symm

/-- The integral identity identification is completeness inverted followed by multiplication.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointIntegralScalarUnit
    (K : completedIntegralDerivedCategory l E
            (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E
            (Spec (.of D.k)) K) :
    (integralScalarExtension.{u} l E E (AlgHom.id ℚ_[l] E)
            (Spec (.of D.k))).obj K ≅ K :=
  (pointConstructibleCompletionIso l E E (AlgHom.id ℚ_[l] E) D hl K hK).symm ≪≫
    (pointDerivedTensorUnit D.k l E).app K

/-- The integral associator is the specified conjugate of the ordinary derived associator.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointIntegralScalarAssoc
    (K : completedIntegralDerivedCategory l E
            (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E
            (Spec (.of D.k)) K) :
    (integralScalarExtension.{u} l L M κ
            (Spec (.of D.k))).obj
        ((integralScalarExtension.{u} l E L ι
            (Spec (.of D.k))).obj K) ≅
      (integralScalarExtension.{u} l E M (κ.comp ι)
            (Spec (.of D.k))).obj K :=
  (pointConstructibleCompletionIso l L M κ D hl _
    (integralScalarExtension_constructible D l hl E L ι
      (Spec (.of D.k)) ⟨K, hK⟩)).symm ≪≫
    (completedDerivedScalarExtension.{u, u} l L M κ
            (Spec (.of D.k))).mapIso
      (pointConstructibleCompletionIso l E L ι D hl K hK).symm ≪≫
    (pointDerivedTensorAssoc D.k l E L ι M κ).app K ≪≫
    pointConstructibleCompletionIso l E M (κ.comp ι) D hl K hK

/-- Rational phi is integral phi tensored with L, followed by the balanced localization map.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointRationalSectionsScalarExtensionIso
    (K : completedIntegralDerivedCategory l E
            (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E
            (Spec (.of D.k)) K) :
    (pointModuleDerivedRationalization l L).obj
        ((pointCompletedDerivedSections D.k l L).obj
          ((integralScalarExtension.{u} l E L ι
            (Spec (.of D.k))).obj K)) ≅
      (pointCoefficientFieldDerivedTensor l E L ι).obj
        ((pointModuleDerivedRationalization l E).obj
          ((pointCompletedDerivedSections D.k l E).obj K)) :=
  (pointModuleDerivedRationalization l L).mapIso
    (pointSectionsScalarExtensionIso l E L ι D hl K hK) ≪≫
      (pointDerivedTensorRationalization l E L ι).app
        ((pointCompletedDerivedSections D.k l E).obj K)

private theorem inverseSquare
    {C : Type a} [Category C] {A B X Y : C}
    (e : A ≅ B) (f : X ≅ Y) (u : A ⟶ X) (v : B ⟶ Y)
    (h : v ≫ f.inv = e.inv ≫ u) : u ≫ f.hom = e.hom ≫ v := by
  apply (cancel_mono f.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h, Iso.hom_inv_id_assoc]

private theorem pointScalarSectionsNatural
    (K J : completedIntegralDerivedCategory l E (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k)) K)
    (hJ : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k)) J)
    (f : K ⟶ J) :
    (pointCompletedDerivedSections D.k l L).map
        ((integralScalarExtension l E L ι (Spec (.of D.k))).map f) ≫
      (pointSectionsScalarExtensionIso l E L ι D hl J hJ).hom =
    (pointSectionsScalarExtensionIso l E L ι D hl K hK).hom ≫
      (pointIntegralModuleDerivedTensor l E L ι).map
        ((pointCompletedDerivedSections D.k l E).map f) := by
  let ψ := (pointDerivedSectionsTensor D.k l E L ι).hom ≫
    Functor.whiskerRight (completedScalarComparison l E L ι (Spec (.of D.k)))
      (pointCompletedDerivedSections D.k l L)
  have hn :
      (pointIntegralModuleDerivedTensor l E L ι).map
          ((pointCompletedDerivedSections D.k l E).map f) ≫
        (pointSectionsScalarExtensionIso l E L ι D hl J hJ).inv =
      (pointSectionsScalarExtensionIso l E L ι D hl K hK).inv ≫
        (pointCompletedDerivedSections D.k l L).map
          ((integralScalarExtension l E L ι (Spec (.of D.k))).map f) := by
    simpa only [ψ, pointSectionsScalarExtensionIso,
      pointConstructibleCompletionIso, Iso.symm_inv, Iso.trans_hom,
      Iso.app_hom, Functor.mapIso_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.comp_map, asIso_hom, integralScalarExtension,
      integralScalarExtensionOfUniverses] using ψ.naturality f
  exact inverseSquare _ _ _ _ hn

private theorem pointScalarSectionsTower
    (K : completedIntegralDerivedCategory l E (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k)) K) :
    (pointCompletedDerivedSections D.k l M).map
        (pointIntegralScalarAssoc l E L ι M κ D hl K hK).hom ≫
      (pointSectionsScalarExtensionIso l E M (κ.comp ι) D hl K hK).hom =
    (pointSectionsScalarExtensionIso l L M κ D hl _
      (integralScalarExtension_constructible D l hl E L ι (Spec (.of D.k)) ⟨K, hK⟩)).hom ≫
      (pointIntegralModuleDerivedTensor l L M κ).map
        (pointSectionsScalarExtensionIso l E L ι D hl K hK).hom ≫
      (pointIntegralModuleDerivedAssoc l E L ι M κ).hom.app
        ((pointCompletedDerivedSections D.k l E).obj K) := by
  let C := pointConstructibleCompletionIso l E L ι D hl K hK
  let S := pointCompletedDerivedSections D.k l M
  let A := completedDerivedScalarExtension l L M κ (Spec (.of D.k))
  have hn := (pointDerivedSectionsTensor D.k l L M κ).inv.naturality C.inv
  simp only [Functor.comp_map] at hn
  simp only [pointIntegralScalarAssoc, pointSectionsScalarExtensionIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc,
    Iso.app_hom, Iso.app_inv, Iso.map_hom_inv_id_assoc]
  rw [pointDerivedSectionsTower]
  rw [reassoc_of% hn]

private theorem pointRationalSectionsNatural
    (K J : completedIntegralDerivedCategory l E (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k)) K)
    (hJ : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k)) J)
    (f : K ⟶ J) :
    (pointModuleDerivedRationalization l L).map
        ((pointCompletedDerivedSections D.k l L).map
          ((integralScalarExtension l E L ι (Spec (.of D.k))).map f)) ≫
      (pointRationalSectionsScalarExtensionIso l E L ι D hl J hJ).hom =
    (pointRationalSectionsScalarExtensionIso l E L ι D hl K hK).hom ≫
      (pointCoefficientFieldDerivedTensor l E L ι).map
        ((pointModuleDerivedRationalization l E).map
          ((pointCompletedDerivedSections D.k l E).map f)) := by
  simp only [pointRationalSectionsScalarExtensionIso, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, pointScalarSectionsNatural, Functor.map_comp_assoc]
  exact congrArg (fun z ↦
    (pointModuleDerivedRationalization l L).map
      (pointSectionsScalarExtensionIso l E L ι D hl K hK).hom ≫ z)
    ((pointDerivedTensorRationalization l E L ι).hom.naturality
      ((pointCompletedDerivedSections D.k l E).map f))

private theorem pointRationalSectionsTower
    (K : completedIntegralDerivedCategory l E (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k)) K) :
    (pointModuleDerivedRationalization l M).map
        ((pointCompletedDerivedSections D.k l M).map
          (pointIntegralScalarAssoc l E L ι M κ D hl K hK).hom) ≫
      (pointRationalSectionsScalarExtensionIso l E M (κ.comp ι) D hl K hK).hom =
    (pointRationalSectionsScalarExtensionIso l L M κ D hl _
      (integralScalarExtension_constructible D l hl E L ι (Spec (.of D.k)) ⟨K, hK⟩)).hom ≫
      (pointCoefficientFieldDerivedTensor l L M κ).map
        (pointRationalSectionsScalarExtensionIso l E L ι D hl K hK).hom ≫
      (pointCoefficientFieldDerivedAssoc l E L ι M κ).hom.app
        ((pointModuleDerivedRationalization l E).obj
          ((pointCompletedDerivedSections D.k l E).obj K)) := by
  simp only [pointRationalSectionsScalarExtensionIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc, Functor.map_comp]
  rw [← Functor.map_comp_assoc, pointScalarSectionsTower]
  simp only [Functor.map_comp, Category.assoc]
  rw [pointRationalizationTower]
  have hn := (pointDerivedTensorRationalization l L M κ).hom.naturality
    (pointSectionsScalarExtensionIso l E L ι D hl K hK).hom
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]

attribute [local irreducible] pointSectionsScalarExtensionIso pointIntegralScalarAssoc
  pointIntegralScalarUnit pointRationalSectionsScalarExtensionIso

set_option linter.all false in
end Constructible

end WeilConjectures
