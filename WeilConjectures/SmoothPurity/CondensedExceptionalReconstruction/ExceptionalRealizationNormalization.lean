/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CondensedExceptionalReconstruction.ExceptionalReconstructionPresentations
public import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedERealizationDefinitions
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteCoefficientAdjointComparisons
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemDerivedComparison
public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemTransport
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleTowerBrownAdjunction
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Clopen.ClopenStrictSystemComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CompactSupportCondensedRealization
import WeilConjectures.SmoothPurity.FilteredCondensedRepresentingPair.FilteredCondensedRepresentingPair
import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
import WeilConjectures.CategoryTheory.Derived.DerivedMorphismPresheaf
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedFlatCoefficientCalculus
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible

/-! # Condensed exceptional inverse image from an ordinary coefficient system

Source: current blueprint sec-smooth-purity, sk-prop-sp-integral-adjunction,
sk-prop-sp-rational, sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical;
WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/UpperShriek.lean,
`boundedConstructibleUpperShriekOfCompactification` and its specifying adjunction.
(blueprint: def-pur-exceptional-realization-normalization).

The coefficient field is the canonical universe lift of Q_l. All systems below are
objects of ordinary derived categories of strict varying-coefficient module sheaves.
The helper records package the constructions and clauses of this node. In particular
no ambient unbounded pro-etale exceptional right adjoint is assumed or constructed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance high] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
  WeilConjectures.PurityFiniteSetting.clopenProEtaleSystemDerived
  WeilConjectures.PurityFiniteSetting.clopenProEtaleLevelDerived
attribute [local semireducible] AlgebraicGeometry.exceptionalProSystemDerived
  AlgebraicGeometry.exceptionalProLevelDerived
attribute [local instance high] CategoryTheory.Functor.preservesZeroMorphisms_of_additive
attribute [local instance high] AlgebraicGeometry.ProEtale.SemilinearProperOpen.pull_additive
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.pull_limits
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.pull_colimits
  SheafOfModules.CoefficientSystemOrdinaryImage.systemInverseAdditive
  SheafOfModules.CoefficientSystemOrdinaryImage.inverseAdditive
  WeilConjectures.PurityFiniteSetting.ClopenSequenceRealizationData.ordinaryAdditive
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
attribute [local irreducible] CategoryTheory.mateEquiv CategoryTheory.conjugateEquiv
attribute [local irreducible] DerivedCategory.Q
  CategoryTheory.Functor.mapDerivedCategoryFactors
attribute [local irreducible] AlgebraicGeometry.ProEtale.SemilinearProperOpen.J
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.R
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.adj
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.rightAdjoint CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
  AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactification
  AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperShriekOfCompactification
universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedExceptionalReconstruction
open CondensedERealization CompactSupportCondensedRealization PurityFiniteSetting

variable (l : ℕ) [Fact l.Prime] (k : Type u) [_root_.Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  (D : CondensedERealization.Data l (Field.{u} l) k)
attribute [local instance] CondensedERealization.At.encodingAdditive
  CondensedERealization.At.encodingInverseAdditive
open AlgebraicGeometry.ProEtale.SemilinearProperOpen

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [local irreducible] WeilConjectures.purCoefficientModel

/-- The composite coefficient inclusion used by U.
Source: blueprint sk-prop-sp-integral-adjunction and sk-prop-sp-rational,
derived scalar extension with its original adjunction and shift comparisons.
(blueprint: def-pur-exceptional-realization-normalization). -/
def normalizationScalarMap (T : Base k) :=
  (D.atObject T).integralIso.hom ≫ (D.atObject T).inclusion

/-- The ambient composite of the three specified derived scalar functors.
Source: blueprint sk-prop-sp-integral-adjunction and sk-prop-sp-rational,
derived scalar extension with its original adjunction and shift comparisons.
(blueprint: def-pur-exceptional-realization-normalization). -/
abbrev normalizationModel (T : Base k) :=
  pbcDerivedExtend (normalizationScalarMap l k D T) ⋙
    (moduleEncoding l (Field.{u} l) T.scheme (D.atObject T).sectionIso).mapDerivedCategory.inverse ⋙
      omegaScalar l (Field.{u} l) (embedding l) T.scheme

/-- Restriction through precisely the same three coefficient maps.
Source: blueprint sk-prop-sp-integral-adjunction and sk-prop-sp-rational,
derived scalar extension with its original adjunction and shift comparisons.
(blueprint: def-pur-exceptional-realization-normalization). -/
abbrev normalizationRestriction (T : Base k) :=
  (Mod.comap (coefficientMap
    (omegaMap l (Field.{u} l) (embedding l)) T.scheme)).mapDerivedCategory ⋙
    (moduleEncoding l (Field.{u} l) T.scheme (D.atObject T).sectionIso).mapDerivedCategory.functor ⋙
      pbcDerivedRestrict (normalizationScalarMap l k D T)

/-- The original composite derived scalar adjunction, including its unit.
Source: blueprint sk-prop-sp-integral-adjunction and sk-prop-sp-rational,
derived scalar extension with its original adjunction and shift comparisons.
(blueprint: def-pur-exceptional-realization-normalization). -/
def normalizationAdjunction (T : Base k) :
    normalizationModel l k D T ⊣ normalizationRestriction l k D T :=
  ((pbcDerivedScalarAdjunction (normalizationScalarMap l k D T)).comp
    (moduleEncoding l (Field.{u} l) T.scheme
      (D.atObject T).sectionIso).mapDerivedCategory.symm.toAdjunction).comp
        (Mod.derivedExtendMapDerivedCategoryAdjunction
          (coefficientMap (omegaMap l (Field.{u} l) (embedding l)) T.scheme))

/-- The recorded realization comparison, extended to the fixed closure.
Source: blueprint sk-prop-sp-integral-adjunction and sk-prop-sp-rational,
derived scalar extension with its original adjunction and shift comparisons.
(blueprint: def-pur-exceptional-realization-normalization). -/
def normalizationComparison (T : Base k) (K : Integral l (Field.{u} l) T.scheme) :
    (normalizationModel l k D T).obj K.obj ≅ ((realization l k D T).obj K).obj :=
  (omegaScalar l (Field.{u} l) (embedding l) T.scheme).mapIso
    (((moduleEncoding l (Field.{u} l) T.scheme
        (D.atObject T).sectionIso).mapDerivedCategory.inverse.mapIso
          ((D.atObject T).scalarExtension.app K).symm) ≪≫
      (moduleEncoding l (Field.{u} l) T.scheme
        (D.atObject T).sectionIso).mapDerivedCategory.unitIso.symm.app _)

/-- Ordinary restriction retains the sectionwise coefficient actions.
Source: blueprint sk-prop-sp-integral-adjunction and sk-prop-sp-rational,
derived scalar extension with its original adjunction and shift comparisons.
(blueprint: def-pur-exceptional-realization-normalization). -/
abbrev normalizationOrdinaryRestriction (T : Base k) :=
  Mod.comap (coefficientMap (omegaMap l (Field.{u} l) (embedding l)) T.scheme) ⋙
    (moduleEncoding l (Field.{u} l) T.scheme (D.atObject T).sectionIso).functor ⋙
      pbcRestrict (normalizationScalarMap l k D T)

/-- The canonical exact-functor composition comparison for restriction.
Source: blueprint sk-prop-sp-integral-adjunction and sk-prop-sp-rational,
derived scalar extension with its original adjunction and shift comparisons.
(blueprint: def-pur-exceptional-realization-normalization). -/
def normalizationRestrictionComparison (T : Base k) :
    (normalizationOrdinaryRestriction l k D T).mapDerivedCategory ≅
      normalizationRestriction l k D T :=
  Functor.mapDerivedCategoryCompIso
    (Mod.comap (coefficientMap (omegaMap l (Field.{u} l) (embedding l)) T.scheme) ⋙
      (moduleEncoding l (Field.{u} l) T.scheme (D.atObject T).sectionIso).functor)
    (pbcRestrict (normalizationScalarMap l k D T)) ≪≫
  Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryCompIso
      (Mod.comap (coefficientMap (omegaMap l (Field.{u} l) (embedding l)) T.scheme))
      (moduleEncoding l (Field.{u} l) T.scheme (D.atObject T).sectionIso).functor)
    (pbcDerivedRestrict (normalizationScalarMap l k D T))

/-- The completed regular coefficient module before passage to complexes.
Source: blueprint sk-prop-sp-integral-adjunction and sk-prop-sp-rational,
derived scalar extension with its original adjunction and shift comparisons.
(blueprint: def-pur-exceptional-realization-normalization). -/
abbrev normalizationRegular (T : Base k) :=
  SheafOfModules.unit ((adicLisseForget T.scheme).obj
    (pbcAdicCompletion T.scheme (pbcIntegralDatum l (Field.{u} l))))

/-- A sectionwise-normalized coefficient map. Its transpose is tensor multiplication.
Source: blueprint sk-prop-sp-integral-adjunction and sk-prop-sp-rational,
derived scalar extension with its original adjunction and shift comparisons.
(blueprint: def-pur-exceptional-realization-normalization). -/
def IsCoefficientInclusion (T : Base k)
    (a : normalizationRegular l k T ⟶
      (normalizationOrdinaryRestriction l k D T).obj
        (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) T.scheme))) : Prop :=
  ∀ (V : T.scheme.ProEtᵒᵖ) (s : (normalizationRegular l k T).val.obj V),
    HEq (a.val.app V s)
      (((coefficientMap (omegaMap l (Field.{u} l) (embedding l)) T.scheme).hom.app V)
        ((D.atObject T).sectionIso.inv.hom.app V
          ((normalizationScalarMap l k D T).hom.app V s)))

/-- Derivation of the section-normalized coefficient map via the canonical single comparison.
Source: blueprint sk-prop-sp-integral-adjunction and sk-prop-sp-rational,
derived scalar extension with its original adjunction and shift comparisons.
(blueprint: def-pur-exceptional-realization-normalization). -/
def normalizationDerivedInclusion (T : Base k)
    (a : normalizationRegular l k T ⟶
      (normalizationOrdinaryRestriction l k D T).obj
        (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) T.scheme))) :
    (DerivedCategory.singleFunctor _ 0).obj (normalizationRegular l k T) ⟶
      (normalizationRestriction l k D T).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) T.scheme))) :=
  (DerivedCategory.singleFunctor _ 0).map a ≫
    ((normalizationOrdinaryRestriction l k D T).mapDerivedCategorySingleFunctor 0).inv.app _ ≫
      (normalizationRestrictionComparison l k D T).hom.app _

/-- The inverse exact encoding carries its canonical derived CommShift.
Source: blueprint sk-prop-sp-integral-adjunction and sk-prop-sp-rational,
derived scalar extension with its original adjunction and shift comparisons.
(blueprint: def-pur-exceptional-realization-normalization). -/
instance normalizationEncodingCommShift (T : Base k) :
    ((moduleEncoding l (Field.{u} l) T.scheme
      (D.atObject T).sectionIso).mapDerivedCategory.inverse).CommShift ℤ := by
  letI := (D.atObject T).encodingAdditive
  letI := (D.atObject T).encodingInverseAdditive
  change ((moduleEncoding l (Field.{u} l) T.scheme
    (D.atObject T).sectionIso).inverse.mapDerivedCategory).CommShift ℤ
  infer_instance

/-- The canonical CommShift of derived scalar extension and exact coefficient extension.
Source: blueprint sk-prop-sp-integral-adjunction and sk-prop-sp-rational,
derived scalar extension with its original adjunction and shift comparisons.
(blueprint: def-pur-exceptional-realization-normalization). -/
instance normalizationModelCommShift (T : Base k) :
    (normalizationModel l k D T).CommShift ℤ := by
  letI : (pbcDerivedRestrict (normalizationScalarMap l k D T)).CommShift ℤ :=
    inferInstanceAs ((pbcRestrict (normalizationScalarMap l k D T)).mapDerivedCategory.CommShift ℤ)
  letI : (pbcDerivedExtend (normalizationScalarMap l k D T)).CommShift ℤ :=
    (pbcDerivedScalarAdjunction (normalizationScalarMap l k D T)).leftAdjointCommShift ℤ
  letI : PreservesFiniteLimits (Mod.extendScalars
      (coefficientMap (omegaMap l (Field.{u} l) (embedding l)) T.scheme)) :=
    omegaExtension_flat l (Field.{u} l) (embedding l) T.scheme
  letI : (omegaScalar l (Field.{u} l) (embedding l) T.scheme).CommShift ℤ :=
    Functor.CommShift.ofIso
      (Mod.extendScalars
        (coefficientMap (omegaMap l (Field.{u} l) (embedding l))
          T.scheme)).leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  unfold normalizationModel
  infer_instance

end WeilConjectures.CondensedExceptionalReconstruction
