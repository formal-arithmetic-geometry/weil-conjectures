/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QbarCoefficientSmoothBaseChange.QbarCoefficientSmoothBaseChange
public import WeilConjectures.SmoothBaseChange.ECoefficientSmoothBaseChange
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowDerivedSmoothBaseChange
public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Identity
public import WeilConjectures.SmoothBaseChange.AdicSmoothBaseChange
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteProetaleSmoothBaseChange
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.AlgebraicGeometry.Abelian.AbelianDerivedExchangePlusCompatibility
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedDirectImageComposition
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationCoherence
public import WeilConjectures.ProEtaleCoefficients.SixFunctorOperationDatum.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.GlobalFiniteLevelCompactSupportBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedExtensionZeroBaseChange
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.Supporting.OperationCoefficientActionData
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteExtensionCompactSupportBaseChange
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCompactSupportExchange
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.QbarCompactSupportBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportFiniteTorsion
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.ScalarLocalization.PbcRationalTransport
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteCompactSupportProetale

import WeilConjectures.SixFunctors.Supporting.IntrinsicQbarCategory
import WeilConjectures.AlgebraicGeometry.Pbc.PbcIntrinsicTowerComplete
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedExchangeCoherence
public import WeilConjectures.SmoothBaseChange.SbcCompletedOperations

import Mathlib.Algebra.Homology.DerivedCategory.Linear
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedExchangeCoherence
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullbackReflection
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCompactSupportUniformRestriction
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedConstructiblePreservation
import all WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
import WeilConjectures.AlgebraicGeometry.Completed.CompletedExtensionZeroComparison
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
import all WeilConjectures.AlgebraicGeometry.Complete.CompleteCompactSupportProetale
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedExtensionZeroComparison
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcConstructibleReductionDirectImage
import all WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeGeometryFibreBound
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension

/-!
# Naturality, identities, pasting, and smoothness of the canonical exchanges

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/fix-lem-exchanges,
clauses (1)--(4) (blueprint: fix-lem-exchanges).

The symbols Ex_* and Ex_! below are the published stage maps themselves:
`Etale.derivedBaseChangeMapPlus`, `ProEtale.derivedBaseChangeMap`,
`sbcExchangeApp`, `sbcRationalExchange`, and `Presentation.exchange` for Ex_*;
`rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`,
`completedCompactSupportExchange`, `finiteExtensionCompactSupportExchangeComponent`,
and the descent of `CbcQbarExchangeModel.exchange` for Ex_!.
There is no additional exchange chosen from an abstract operation datum.
-/

-- Keep the original compact-support module's derived-localization instance while
-- elaborating its lifted helpers; the generic imported instance has an unresolved
-- maximum coefficient universe at this fixed small-site coefficient size.
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory

attribute [local irreducible] HasDerivedCategory.standard

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme
variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
private instance exchangeDatumModuleLinear (T : Scheme.{u}) :
    Linear A (reductionModules T (d.completedRing T)) := by
  exact pbcCompletedModulesLinear T d
private instance exchangeDatumDerivedLinear (T : Scheme.{u}) :
    Linear A (d.derived T) := inferInstance
private theorem exchangePushLinear {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (d.push f).Linear A := by
  rw [datumPush_eq_actualPush]
  exact (pbcActualOperations_linear_aux f d).2.1

private theorem exchangePullLinear {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (d.pull f).Linear A := by
  have hP : (proEtaleRingModulePullback f (d.completedRing Y) (d.completedRing X)
      (d.integralRingIso f)).Linear A := by
    constructor
    intro M N k a
    have h := (completedModulePullLinear f d).map_smul k a
    rw [coefficientIso_eq f d] at h
    exact h
  have := hP
  exact inferInstanceAs ((proEtaleRingModulePullback f (d.completedRing Y)
    (d.completedRing X) (d.integralRingIso f)).mapDerivedCategory.Linear A)

private theorem exchangeCompletedPullLinear {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (d.completedPull f).Linear A := by
  have := exchangePullLinear d f
  rw [Functor.linear_iff]
  intro K a
  apply ((d.completedPull_reflection f).2 K _
    ((d.completedPull_reflection f).1 K)).1
  dsimp only
  rw [← ordinaryToCompleted_naturality d f (a • 𝟙 K)]
  simp only [Functor.map_smul, Linear.smul_comp, Linear.comp_smul,
    Category.comp_id]
  rw [(d.pull f).map_id K]
  simp only [Category.id_comp]

private theorem exchangeOpenShriekLinear {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] : (cbcDerivedOpenShriek d j inferInstance).Linear A := by
  have hP : (proEtaleRingModulePullback j (d.completedRing T) (d.completedRing U)
      (d.integralRingIso j)).Linear A := by
    constructor
    intro M N f a
    have h := (completedModulePullLinear j d).map_smul f a
    rw [coefficientIso_eq j d] at h
    exact h
  have := hP
  have := cbcPullToRestriction_isIso d j
  have hR : (cbcOpenRestriction d j inferInstance).Linear A :=
    Functor.linear_of_iso A (asIso (cbcPullToRestriction d j))
  have := hR
  have := (cbcOpenAdjunction d j inferInstance).left_adjoint_linear (R := A)
  exact inferInstanceAs ((cbcOpenShriek d j inferInstance).mapDerivedCategory.Linear A)
end AlgebraicGeometry.Scheme

section LiftedCompactSupportInterface

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme.LiftedCbc

/-- The source lift whose objects retain the constructibility witness.
Source: the integral category restriction in the proof
(blueprint: fix-lem-exchanges). -/
abbrev cbcCompactSupportSourceLift
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} (g : Y' ⟶ Y) (c : Compactification f)
    (d : AdicCoefficientDatum (PbcIntegralRing l E))
    (hSource : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportSource g c d).obj K.obj)) :
    PbcBoundedConstructibleComplete X d ⥤
      PbcBoundedConstructibleComplete Y' d :=
  by
    letI := cbcCompactSupportSource_additive g c d
    exact ObjectProperty.liftFullSubcategory
      (PbcIsBoundedConstructibleComplete X d) (PbcIsBoundedConstructibleComplete Y' d)
      (cbcCompactSupportSource g c d) (fun K hK ↦ hSource ⟨K, hK⟩)

/-- The target lift whose objects retain the constructibility witness.
Source: the integral category restriction in the proof
(blueprint: fix-lem-exchanges). -/
abbrev cbcCompactSupportTargetLift
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} (g' : X' ⟶ X)
    (c' : Compactification f')
    (d : AdicCoefficientDatum (PbcIntegralRing l E))
    (hTarget : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportTarget g' c' d).obj K.obj)) :
    PbcBoundedConstructibleComplete X d ⥤
      PbcBoundedConstructibleComplete Y' d :=
  by
    letI := cbcCompactSupportTarget_additive g' c' d
    exact ObjectProperty.liftFullSubcategory
      (PbcIsBoundedConstructibleComplete X d) (PbcIsBoundedConstructibleComplete Y' d)
      (cbcCompactSupportTarget g' c' d) (fun K hK ↦ hTarget ⟨K, hK⟩)

/-- The source restriction is additive for the inherited full-subcategory addition.
Proof: the restriction maps each morphism by the ambient composite. Its additivity
equation is the ambient equation viewed through the faithful full inclusion.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: fix-lem-exchanges). -/
@[instance] theorem cbcCompactSupportSourceLift_additive
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} (g : Y' ⟶ Y) (c : Compactification f)
    (d : AdicCoefficientDatum (PbcIntegralRing l E))
    (hSource : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportSource g c d).obj K.obj)) :
    (cbcCompactSupportSourceLift l E g c d hSource).Additive := by
  let := cbcCompactSupportSource_additive g c d
  exact ObjectProperty.liftFullSubcategory_additive
    (PbcIsBoundedConstructibleComplete X d) (PbcIsBoundedConstructibleComplete Y' d)
    (cbcCompactSupportSource g c d) (fun K hK ↦ hSource ⟨K, hK⟩)

/-- The target restriction is additive for the inherited full-subcategory addition.
Proof: the restriction maps each morphism by the ambient composite. Its additivity
equation is the ambient equation viewed through the faithful full inclusion.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: fix-lem-exchanges). -/
@[instance] theorem cbcCompactSupportTargetLift_additive
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} (g' : X' ⟶ X)
    (c' : Compactification f')
    (d : AdicCoefficientDatum (PbcIntegralRing l E))
    (hTarget : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportTarget g' c' d).obj K.obj)) :
    (cbcCompactSupportTargetLift l E g' c' d hTarget).Additive := by
  let := cbcCompactSupportTarget_additive g' c' d
  exact ObjectProperty.liftFullSubcategory_additive
    (PbcIsBoundedConstructibleComplete X d) (PbcIsBoundedConstructibleComplete Y' d)
    (cbcCompactSupportTarget g' c' d) (fun K hK ↦ hTarget ⟨K, hK⟩)

/-- The source restriction respects the actual constant-section scalar action.
Proof: tensor, pullback and direct image commute with scalar multiples of maps on
representatives. These equations survive localization and full-subcategory restriction.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: fix-lem-exchanges). -/
@[instance] theorem cbcCompactSupportSourceLift_linear
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} (g : Y' ⟶ Y) (c : Compactification f)
    (d : AdicCoefficientDatum (PbcIntegralRing l E))
    (hSource : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportSource g c d).obj K.obj)) :
    (cbcCompactSupportSourceLift l E g c d hSource).Linear
      (PbcIntegralRing l E) := by
  have := exchangeOpenShriekLinear d c.i
  have := exchangePushLinear d c.g
  have := exchangeCompletedPullLinear d g
  constructor
  intro K H f a
  apply ObjectProperty.hom_ext
  exact (cbcCompactSupportSource g c d).map_smul a f.hom

/-- The target restriction respects the actual constant-section scalar action.
Proof: tensor, pullback and direct image commute with scalar multiples of maps on
representatives. These equations survive localization and full-subcategory restriction.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: fix-lem-exchanges). -/
@[instance] theorem cbcCompactSupportTargetLift_linear
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} (g' : X' ⟶ X)
    (c' : Compactification f')
    (d : AdicCoefficientDatum (PbcIntegralRing l E))
    (hTarget : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportTarget g' c' d).obj K.obj)) :
    (cbcCompactSupportTargetLift l E g' c' d hTarget).Linear
      (PbcIntegralRing l E) := by
  have := exchangeCompletedPullLinear d g'
  have := exchangeOpenShriekLinear d c'.i
  have := exchangePushLinear d c'.g
  constructor
  intro K H f a
  apply ObjectProperty.hom_ext
  exact (cbcCompactSupportTarget g' c' d).map_smul a f.hom

/-- The two rational functors obtained by scalar transport of these lifts.
Source: `prop-weil-pbc-rational-transport`
(blueprint: fix-lem-exchanges). -/
abbrev cbcCompactSupportSourceTransport
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} (g : Y' ⟶ Y) (c : Compactification f)
    (d : AdicCoefficientDatum (PbcIntegralRing l E))
    (hSource : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportSource g c d).obj K.obj)) :=
  ScalarLocalization.transport (PbcIntegralRing l E)
    (pbcUniformizer l E)
    (cbcCompactSupportSourceLift l E g c d hSource)

/-- The target rational functor obtained by scalar transport of the target lift.
Source: `prop-weil-pbc-rational-transport`
(blueprint: fix-lem-exchanges). -/
abbrev cbcCompactSupportTargetTransport
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} (g' : X' ⟶ X)
    (c' : Compactification f')
    (d : AdicCoefficientDatum (PbcIntegralRing l E))
    (hTarget : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportTarget g' c' d).obj K.obj)) :=
  ScalarLocalization.transport (PbcIntegralRing l E)
    (pbcUniformizer l E)
    (cbcCompactSupportTargetLift l E g' c' d hTarget)

/-- The canonical scalar-localized component for one integral representative.
Source: the completed exchange in the compact-support square
(blueprint: fix-lem-exchanges). -/
def finiteExtensionCompactSupportExchangeComponent
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (c : Compactification f)
    (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
    (openSquare : OpenImmersionSquare g' c'.i c.i gbar) [QuasiCompact f]
    (r : ℕ) (a : Fin r → PbcIntegralRing l E)
    (ha : Ideal.span (Set.range a) = (pbcIntegralDatum l E).ideal)
    (hSource : ∀ K : PbcBoundedConstructibleComplete X
      (pbcIntegralDatum l E),
      PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum l E)
      (((pbcIntegralDatum l E).completedPull g).obj
        (((pbcIntegralDatum l E).push c.g).obj
          ((cbcDerivedOpenShriek (pbcIntegralDatum l E) c.i
            c.isOpenImmersion).obj K.obj))))
    (hTarget : ∀ K : PbcBoundedConstructibleComplete X
      (pbcIntegralDatum l E),
      PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum l E)
      (((pbcIntegralDatum l E).push c'.g).obj
        ((cbcDerivedOpenShriek (pbcIntegralDatum l E) c'.i
          c'.isOpenImmersion).obj
          (((pbcIntegralDatum l E).completedPull g').obj K.obj))))
    (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E))
    (hComplete : cbcCompleteProperty (pbcIntegralDatum l E) X r a ha K.obj) :
    (cbcCompactSupportSourceTransport l E g c
      (pbcIntegralDatum l E) hSource).obj ⟨K⟩ ⟶
    (cbcCompactSupportTargetTransport l E g' c'
      (pbcIntegralDatum l E) hTarget).obj ⟨K⟩ :=
  (pbcRationalization Y' (pbcIntegralDatum l E)
    (pbcUniformizer l E)).map
    (ObjectProperty.homMk
      (completedCompactSupportExchange (pbcIntegralDatum l E)
        c c' gbar properSquare openSquare r a ha ⟨K.obj, hComplete⟩))

/-- Intrinsic completeness of a selected integral object, for every presentation of I.
Source: blueprint thm-cbc-finite-extension, proof step 2
(blueprint: fix-lem-exchanges).
Proof: membership includes invertibility of the intrinsic Koszul completion unit on
some generating tuple and representative. The canonical coefficient comparison transports
that unit, retaining its normalization. Koszul reconstruction identifies it with the
canonical quotient-tower completion map. For any other finite tuple generating the same
ideal and any other representative, reconstruction identifies its unit with that same map,
conjugated by the representative comparison. Its invertibility is therefore unchanged.
Use the specified Q preimage representative to obtain cbcCompleteProperty. This also
covers the empty tuple when it generates the ideal; no completeness hypothesis is added. -/
theorem finiteExtension_cbcComplete
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) (K : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E))
    (r : ℕ) (a : Fin r → PbcIntegralRing l E)
    (ha : Ideal.span (Set.range a) = (pbcIntegralDatum l E).ideal) :
    cbcCompleteProperty (pbcIntegralDatum l E) T r a ha K.obj := by
  exact ((pbcIntegralDatum l E).towerComplete_iff_intrinsic T K.obj).mp
    (pbcIntrinsicComplete_towerComplete (pbcIntegralDatum l E) T K.obj K.property.1)
    r a ha _ _

/-- Localization of an ambient arrow between selected integral objects.
Applied to a path, this is its rational path: the full inclusion and localization preserve
composition and identities. In particular the following equations use the actual canonical
integral comparisons, with no arbitrary endpoint isomorphism.
Source: blueprint thm-cbc-finite-extension, proof steps 3 and 6
(blueprint: fix-lem-exchanges). -/
def finiteExtensionRationalArrow
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {T : Scheme.{u}} {M N : (pbcIntegralDatum l E).derived T}
    (hM : PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) M)
    (hN : PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) N)
    (v : M ⟶ N) :
    (pbcRationalization T (pbcIntegralDatum l E)
      (pbcUniformizer l E)).obj ⟨M, hM⟩ ⟶
    (pbcRationalization T (pbcIntegralDatum l E)
      (pbcUniformizer l E)).obj ⟨N, hN⟩ :=
  (pbcRationalization T (pbcIntegralDatum l E)
    (pbcUniformizer l E)).map (ObjectProperty.homMk v)

section Coherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

end Coherence

end AlgebraicGeometry.Scheme.LiftedCbc

end

end LiftedCompactSupportInterface

attribute [instance] WeilConjectures.IntegralHom.derivedCategory

@[expose] public noncomputable section
set_option cleanup.letToHave false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory CategoryTheory.TwoSquare
open scoped CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Etale
namespace WeilConjectures

open AlgebraicGeometry.Scheme.QbarCoefficientSmoothBaseChange
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Select the inherited finite-stage category instance at its already prescribed size.
Source: fix-lem-exchanges, common-stage conventions (blueprint: fix-lem-exchanges). -/
local instance exchangeStageCategory (l : ℕ) [Fact l.Prime] (Ω : Type v)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T : Scheme.{u}) (i : Padic.FiniteCoefficientFields l Ω) :
    Category.{u + 2} (pbcStageCategory.{u, v} l Ω T i) := inferInstance
/-- Select the inherited ambient Karoubi-stage category instance at its prescribed size.
Source: fix-lem-exchanges, common-stage conventions (blueprint: fix-lem-exchanges). -/
local instance exchangeAmbientStageCategory (l : ℕ) [Fact l.Prime] (Ω : Type v)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T : Scheme.{u}) (i : Padic.FiniteCoefficientFields l Ω) :
    Category.{u + 2} (pbcAmbientCompleteKaroubiStage.{u, v} l Ω T i) := inferInstance
/-- Select the inherited additive structure on the finite coefficient stage.
Source: fix-lem-exchanges, common-stage scalar transport (blueprint: fix-lem-exchanges). -/
local instance exchangeStagePreadditive (l : ℕ) [Fact l.Prime] (Ω : Type v)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T : Scheme.{u}) (i : Padic.FiniteCoefficientFields l Ω) :
    Preadditive.{u + 2, u + 2} (pbcStageCategory.{u, v} l Ω T i) := inferInstance

section
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
  [IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [dS : Fact (∃ n : ℕ, topologicalKrullDim S ≤ n)]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  (sq : ChosenCartesianSquare h e f g)

end

section
variable (l : ℕ) [Fact l.Prime] (Ω : Type v)
  [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X' X Y' Y : Scheme.{u}}
  {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
  (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
  (openSquare : OpenImmersionSquare g' c'.i c.i gbar)
  [QuasiCompact f]
  [IsNoetherian X] [IsNoetherian Y']
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
  [iY' : Fact (∀ y : Y', IsUnit (l : Y'.presheaf.stalk y))]

end

end WeilConjectures
