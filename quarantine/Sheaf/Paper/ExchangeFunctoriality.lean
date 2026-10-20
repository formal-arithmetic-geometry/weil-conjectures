/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Paper.QbarCoefficientSmoothBaseChange
public import Sheaf.Paper.ECoefficientSmoothBaseChange
public import Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange
public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Identity
public import Sheaf.Paper.AdicSmoothBaseChange
public import Sheaf.AlgebraicGeometry.FiniteProetaleSmoothBaseChange
public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
public import Sheaf.AlgebraicGeometry.AbelianDerivedExchangePlusCompatibility
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.Paper.ExchangeIdentityPasting
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.CondensedAmbientExchange
public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.Paper.CompactificationCoherence
public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange
public import Sheaf.Paper.BasicOperationsCoefficientReduction
public import Sheaf.Paper.FiniteExtensionCompactSupportBaseChange
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.CompletedCompactSupportExchange
public import Sheaf.Paper.QbarCompactSupportBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
public import Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
public import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange
import Sheaf.Paper.RefinementComparisonIsomorphism
import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.CompletedCoefficientPushforwardComparison
import Sheaf.Paper.SfCbcCompactSupportCompositionLimit
import Sheaf.Paper.SfCbcExtensionZeroCompletion
import Sheaf.Paper.CompletedPullbackAdjunction
import Sheaf.Paper.ProEtaleConstantReductionTower
import Sheaf.Paper.ProperOpenTowerComparison
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.ConstantCompletionEquivalence
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.StrictTowerExchangeMateNormalization
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
public import Sheaf.Paper.PbcRationalTransport
public import Sheaf.Paper.CompleteCompactSupportProetale
import WeilConjectures.Compactification.NagataCompactification




import Sheaf.Paper.IntrinsicQbarCategory



























public import Sheaf.Paper.CompletedExchangeCoherence
public import Sheaf.Paper.SbcCompletedOperations


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

section LiftedCompactSupportInterface

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
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
  sorry

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
  sorry

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
  sorry

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
  sorry

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

/-- The compact-support exchange over a finite extension is the rational
extension of the completed integral exchange.  It is natural in rational
morphisms and every component is invertible.
Source: blueprint thm-cbc-finite-extension, proof steps 1--6
(blueprint: fix-lem-exchanges).
Proof:
1. The integral compact-support uniform-restriction theorem gives exact scalar-linear
restrictions of Rp_* j_! for f and its base change. The valuation ring has a length-one
free resolution of each quotient. A bounded input therefore has one common reduction
interval. Apply preservation-constructible to the proper identity square with N=l and
fibre bound zero to obtain constructible preservation by both completed pullbacks.
2. Each integral object is intrinsically complete and has compatible etale origins.
Apply thm-cbc-complete-proetale to its specified completed compact-support exchange.
The landing predicates of step 1 put both endpoints in the full integral category;
its inverse is consequently a morphism in that full category as well.
3. Rational transport extends these scalar-linear functors and their natural exchange.
On each Hom module the extended map sends u tensor a to F(u) tensor a, so extensions
of composites agree with composites of extensions.
4. Tensor the integral inverse with one. The localization composition formula makes
its two composites the localized identities, proving every rational component invertible.
5. Integral naturality extends from pure tensors to every rational map by additivity.
For a rational isomorphism identifying two representatives, this equation is exactly
independence of lattice under the two induced functorial identifications.
6. Localize the integral identity and pasting diagrams. Localization preserves identities,
composition and whiskering, and the intermediate comparison maps cancel as integrally. -/
theorem finiteExtension_compactSupportBaseChange
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (c : Compactification f)
    (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
    (openSquare : OpenImmersionSquare g' c'.i c.i gbar)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    (_dimX : ∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (_dimY : ∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))
    (_dimX' : ∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))
    (_dimY' : ∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))
    (_hlX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hlY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (_hlX' : ∀ x' : X', IsUnit (l : X'.presheaf.stalk x'))
    (_hlY' : ∀ y' : Y', IsUnit (l : Y'.presheaf.stalk y')) :
    ∃ (hSource : ∀ K : PbcBoundedConstructibleComplete X
        (pbcIntegralDatum l E),
      PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum l E)
        ((cbcCompactSupportSource g c (pbcIntegralDatum l E)).obj K.obj)),
      ∃ (hTarget : ∀ K : PbcBoundedConstructibleComplete X
        (pbcIntegralDatum l E),
      PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum l E)
        ((cbcCompactSupportTarget g' c' (pbcIntegralDatum l E)).obj K.obj)),
      ∃ η : cbcCompactSupportSourceTransport l E g c
          (pbcIntegralDatum l E) hSource ≅
        cbcCompactSupportTargetTransport l E g' c'
          (pbcIntegralDatum l E) hTarget,
        ∀ (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E))
          (r : ℕ) (a : Fin r → PbcIntegralRing l E)
          (ha : Ideal.span (Set.range a) = (pbcIntegralDatum l E).ideal)
          (hComplete : cbcCompleteProperty (pbcIntegralDatum l E) X r a ha K.obj),
          η.hom.app ⟨K⟩ =
            finiteExtensionCompactSupportExchangeComponent l E c c' gbar
              properSquare openSquare r a ha hSource hTarget K hComplete := by
  sorry

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
  sorry

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

/-- Rational identity-base-change coherence, with the unit-normalized completed identity
comparisons. Both paths are localized in the raw rational category of Y.
Source: blueprint thm-cbc-finite-extension, identity clause and proof step 6
(blueprint: fix-lem-exchanges).
Proof: apply completeCompactSupportProetale_identity to the complete integral object
with its compatible origins. Integral compact support and completed pullback land in the
selected subcategories by proof step 1. Regard both paths as morphisms of the full integral
subcategory and apply its rationalization functor. This functor preserves compositions and
identities, giving precisely the displayed rational paths. The component formula of the
main theorem identifies their exchange with the rational natural isomorphism. -/
theorem finiteExtension_compactSupportBaseChange_identity
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hX : CbcFiniteExtensionDomain l X) (_hY : CbcFiniteExtensionDomain l Y)
    (c : Compactification f)
    (sp : ChosenCartesianSquare (𝟙 c.Z) c.g c.g (𝟙 Y))
    (sj : OpenImmersionSquare (𝟙 X) c.i c.i (𝟙 c.Z))
    (r : ℕ) (a : Fin r → PbcIntegralRing l E)
    (ha : Ideal.span (Set.range a) = (pbcIntegralDatum l E).ideal)
    (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)) :
    ∃ (hK : (pbcIntegralDatum l E).TowerComplete X K.obj)
      (hF : (pbcIntegralDatum l E).TowerComplete Y
        ((cbcSupport (pbcIntegralDatum l E) c).obj K.obj))
      (hS : PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E)
        (((pbcIntegralDatum l E).completedPull (𝟙 Y)).obj
          ((cbcSupport (pbcIntegralDatum l E) c).obj K.obj)))
      (hT : PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E)
        ((cbcSupport (pbcIntegralDatum l E) c).obj K.obj)),
      finiteExtensionRationalArrow l E hS hT
        (cbcExchange (pbcIntegralDatum l E) c c (𝟙 c.Z) sp sj r a ha
            ⟨K.obj, finiteExtension_cbcComplete l E X K r a ha⟩ ≫
          (cbcSupport (pbcIntegralDatum l E) c).map
            ((pbcIntegralDatum l E).completedPullId X K.obj hK).hom) =
      finiteExtensionRationalArrow l E hS hT
        ((pbcIntegralDatum l E).completedPullId Y
          ((cbcSupport (pbcIntegralDatum l E) c).obj K.obj) hF).hom := by
  sorry

/-- Rational horizontal-pasting coherence for two arbitrary successive base changes.
The paths retain the canonical completion-unit-normalized pullback compositors.
Source: blueprint thm-cbc-finite-extension, pasted-square clause and proof step 6
(blueprint: fix-lem-exchanges).
Proof: proof step 1 gives constructible complete landing for the intermediate pullback
and all endpoints. Apply completeCompactSupportProetale_horizontal, using the input's
intrinsic completeness and compatible etale origins. Localize its two paths in the full
selected category of Y''. Functoriality of localization and the pure-tensor formula for
scalar transport identify these with the two rational pasted paths. The main component
formula identifies every exchange factor with its specified rational component. -/
theorem finiteExtension_compactSupportBaseChange_horizontal
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hX : CbcFiniteExtensionDomain l X) (_hX' : CbcFiniteExtensionDomain l X')
    (_hX'' : CbcFiniteExtensionDomain l X'') (_hY : CbcFiniteExtensionDomain l Y)
    (_hY' : CbcFiniteExtensionDomain l Y') (_hY'' : CbcFiniteExtensionDomain l Y'')
    (c : Compactification f) (c' : Compactification f') (c'' : Compactification f'')
    (gb : c'.Z ⟶ c.Z) (hb : c''.Z ⟶ c'.Z)
    (sp₁ : ChosenCartesianSquare gb c'.g c.g g)
    (sj₁ : OpenImmersionSquare g' c'.i c.i gb)
    (sp₂ : ChosenCartesianSquare hb c''.g c'.g h)
    (sj₂ : OpenImmersionSquare h' c''.i c'.i hb)
    (sp : ChosenCartesianSquare (hb ≫ gb) c''.g c.g (h ≫ g))
    (sj : OpenImmersionSquare (h' ≫ g') c''.i c.i (hb ≫ gb))
    (r : ℕ) (a : Fin r → PbcIntegralRing l E)
    (ha : Ideal.span (Set.range a) = (pbcIntegralDatum l E).ideal)
    (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)) :
    ∃ (hK' : cbcCompleteProperty (pbcIntegralDatum l E) X' r a ha
        (((pbcIntegralDatum l E).completedPull g').obj K.obj))
      (hS : PbcIsBoundedConstructibleComplete Y'' (pbcIntegralDatum l E)
        (((pbcIntegralDatum l E).completedPull (h ≫ g)).obj
          ((cbcSupport (pbcIntegralDatum l E) c).obj K.obj)))
      (hT : PbcIsBoundedConstructibleComplete Y'' (pbcIntegralDatum l E)
        ((cbcSupport (pbcIntegralDatum l E) c'').obj
          (((pbcIntegralDatum l E).completedPull (h' ≫ g')).obj K.obj))),
      finiteExtensionRationalArrow l E hS hT
        (cbcExchange (pbcIntegralDatum l E) c c'' (hb ≫ gb) sp sj r a ha
          ⟨K.obj, finiteExtension_cbcComplete l E X K r a ha⟩) =
      finiteExtensionRationalArrow l E hS hT
        (((pbcIntegralDatum l E).completedPullComp h g).hom.app
            ((cbcSupport (pbcIntegralDatum l E) c).obj K.obj) ≫
          ((pbcIntegralDatum l E).completedPull h).map
            (cbcExchange (pbcIntegralDatum l E) c c' gb sp₁ sj₁ r a ha
              ⟨K.obj, finiteExtension_cbcComplete l E X K r a ha⟩) ≫
          cbcExchange (pbcIntegralDatum l E)
            (qf := cbcBaseChangeQuasiCompact c c' gb sj₁)
            c' c'' hb sp₂ sj₂ r a ha
            ⟨((pbcIntegralDatum l E).completedPull g').obj K.obj, hK'⟩ ≫
          (cbcSupport (pbcIntegralDatum l E) c'').map
            (((pbcIntegralDatum l E).completedPullComp h' g').inv.app K.obj)) := by
  sorry

/-- Rational vertical-pasting coherence, with the canonical proper/open composition
maps for supplied compatible compactification towers. No Cartesian refinement is imposed.
Source: blueprint thm-cbc-finite-extension, pasted-square clause and proof step 6
(blueprint: fix-lem-exchanges).
Proof: compact-support preservation in proof step 1 supplies the complete intermediate
image and all constructible endpoints. Apply completeCompactSupportProetale_vertical
with the input's compatible origins. Its comparisons are the specified proper/open mates
and are invertible. Localize its two ordered paths. Preservation of composition and the
scalar-transport formula identify these with rational vertical pasting. The integral
composition/refinement law makes the same equation valid after any common refinement,
so the supplied compatible towers do not restrict the allowed pasted squares. -/
theorem finiteExtension_compactSupportBaseChange_vertical
    {X X' Y Y' Z Z' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {h : Y ⟶ Z} {h' : Y' ⟶ Z'}
    {gx : X' ⟶ X} {gy : Y' ⟶ Y} {gz : Z' ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (_hX : CbcFiniteExtensionDomain l X) (_hX' : CbcFiniteExtensionDomain l X')
    (_hY : CbcFiniteExtensionDomain l Y) (_hY' : CbcFiniteExtensionDomain l Y')
    (_hZ : CbcFiniteExtensionDomain l Z) (_hZ' : CbcFiniteExtensionDomain l Z')
    (cf : Compactification f) (ch : Compactification h)
    (chf : Compactification (f ≫ h))
    (cf' : Compactification f') (ch' : Compactification h')
    (chf' : Compactification (f' ≫ h'))
    (gbf : cf'.Z ⟶ cf.Z) (gbh : ch'.Z ⟶ ch.Z) (gbhf : chf'.Z ⟶ chf.Z)
    (spf : ChosenCartesianSquare gbf cf'.g cf.g gy)
    (sjf : OpenImmersionSquare gx cf'.i cf.i gbf)
    (sph : ChosenCartesianSquare gbh ch'.g ch.g gz)
    (sjh : OpenImmersionSquare gy ch'.i ch.i gbh)
    (sphf : ChosenCartesianSquare gbhf chf'.g chf.g gz)
    (sjhf : OpenImmersionSquare gx chf'.i chf.i gbhf)
    (b : cf.Z ⟶ chf.Z) (p : chf.Z ⟶ ch.Z)
    (b' : cf'.Z ⟶ chf'.Z) (p' : chf'.Z ⟶ ch'.Z)
    [IsProper p] [IsProper p']
    (hb : cf.i ≫ b = chf.i) (hp : b ≫ p = cf.g ≫ ch.i)
    (hq : p ≫ ch.g = chf.g)
    (hb' : cf'.i ≫ b' = chf'.i) (hp' : b' ≫ p' = cf'.g ≫ ch'.i)
    (hq' : p' ≫ ch'.g = chf'.g)
    (sq : IsPullback b cf.g p ch.i) (sq' : IsPullback b' cf'.g p' ch'.i)
    (_wb : b' ≫ gbhf = gbf ≫ b) (_wp : p' ≫ gbh = gbhf ≫ p)
    (r : ℕ) (a : Fin r → PbcIntegralRing l E)
    (ha : Ideal.span (Set.range a) = (pbcIntegralDatum l E).ideal)
    (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)) :
    ∃ (hF : cbcCompleteProperty (pbcIntegralDatum l E) Y r a ha
        ((cbcSupport (pbcIntegralDatum l E) cf).obj K.obj))
      (hS : PbcIsBoundedConstructibleComplete Z' (pbcIntegralDatum l E)
        (((pbcIntegralDatum l E).completedPull gz).obj
          ((cbcSupport (pbcIntegralDatum l E) ch).obj
            ((cbcSupport (pbcIntegralDatum l E) cf).obj K.obj))))
      (hT : PbcIsBoundedConstructibleComplete Z' (pbcIntegralDatum l E)
        ((cbcSupport (pbcIntegralDatum l E) chf').obj
          (((pbcIntegralDatum l E).completedPull gx).obj K.obj))),
      finiteExtensionRationalArrow l E hS hT
        (((pbcIntegralDatum l E).completedPull gz).map
            (cbcTowerCompositionMap (pbcIntegralDatum l E)
              cf ch chf b p hb hp hq sq K.obj) ≫
          cbcExchange (pbcIntegralDatum l E) chf chf' gbhf sphf sjhf r a ha
            ⟨K.obj, finiteExtension_cbcComplete l E X K r a ha⟩) =
      finiteExtensionRationalArrow l E hS hT
        (cbcExchange (pbcIntegralDatum l E) ch ch' gbh sph sjh r a ha
            ⟨(cbcSupport (pbcIntegralDatum l E) cf).obj K.obj, hF⟩ ≫
          (cbcSupport (pbcIntegralDatum l E) ch').map
            (cbcExchange (pbcIntegralDatum l E) cf cf' gbf spf sjf r a ha
              ⟨K.obj, finiteExtension_cbcComplete l E X K r a ha⟩) ≫
          cbcTowerCompositionMap (pbcIntegralDatum l E)
            (qh := cbcBaseChangeQuasiCompact ch ch' gbh sjh)
            cf' ch' chf' b' p' hb' hp' hq' sq'
            (((pbcIntegralDatum l E).completedPull gx).obj K.obj)) := by
  sorry

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
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory CategoryTheory.TwoSquare
open scoped CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Etale
namespace WeilConjectures

/-- Identity and the two pasting equations for the finite constant-module mate.
Source: blueprint fix-lem-exchanges, clauses (1)--(4)
(blueprint: fix-lem-exchanges). -/
@[irreducible] def exchangeFiniteOrdinaryLaws (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] : Prop :=
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (sq : CommSq (𝟙 X) f f (𝟙 Y)),
  Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq =
        Functor.whiskerLeft (f)_*[(ModuleCat.{u + 1} Λ)].rightDerivedFunctorPlus
      (Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) Y).hom ≫
          (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
          Functor.whiskerRight (Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv
            (f)_*[(ModuleCat.{u + 1} Λ)].rightDerivedFunctorPlus) ∧
  (∀ {X X' X'' Y Y' Y'' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''} {g : Y' ⟶ Y} {g'
      : X' ⟶ X} {g'' : X'' ⟶ X'} {h : Y'' ⟶ Y'} (sq₁ : CommSq g' f' f g)
      (sq₂ : CommSq g'' f'' f' h) (sq : CommSq (g'' ≫ g') f'' f (h ≫ g)),
  Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq =
        Functor.whiskerLeft (f)_*[(ModuleCat.{u + 1} Λ)].rightDerivedFunctorPlus
            (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) h g).hom ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₁)
            ((h)^*[(ModuleCat.{u + 1} Λ)]).mapDerivedCategoryPlus ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft ((g')^*[(ModuleCat.{u + 1} Λ)]).mapDerivedCategoryPlus
            (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₂) ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) g'' g').inv
            (f'')_*[(ModuleCat.{u + 1} Λ)].rightDerivedFunctorPlus) ∧
  (∀ {X X' Y Y' Z Z' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X} {e : Y ⟶
      Z} {e' : Y' ⟶ Z'} {k : Z' ⟶ Z} (sq₁ : CommSq g' f' f g)
      (sq₂ : CommSq g e' e k) (sq : CommSq g' (f' ≫ e') (f ≫ e) k),
  Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq =
        Functor.whiskerRight (Functor.rightDerivedFunctorPlusCompIso' (f)_*[(ModuleCat.{u + 1} Λ)]
      (e)_*[(ModuleCat.{u + 1} Λ)]
            (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) f e)).inv ((k)^*[(ModuleCat.{u + 1}
      Λ)]).mapDerivedCategoryPlus ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (f)_*[(ModuleCat.{u + 1} Λ)].rightDerivedFunctorPlus
            (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₂) ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₁)
            (e')_*[(ModuleCat.{u + 1} Λ)].rightDerivedFunctorPlus ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft ((g')^*[(ModuleCat.{u + 1} Λ)]).mapDerivedCategoryPlus
            (Functor.rightDerivedFunctorPlusCompIso' (f')_*[(ModuleCat.{u + 1} Λ)]
      (e')_*[(ModuleCat.{u + 1} Λ)]
              (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) f' e')).hom)

/-- Completed ordinary coherence on the proper witnessed domain. The datum is a
parameter; the main assertion specializes it to the item's coefficient integers.
Source: fix-lem-exchanges, clauses (1)--(2)
(blueprint: fix-lem-exchanges). -/
@[irreducible] def CompletedOrdinaryExchangeLaws {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : Prop :=
  (∀  {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
      {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) [IsProper f]
      (K H : d.derived X) (_hK : d.TowerComplete X K) (hH : d.TowerComplete X H)
      (WK : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
        ((d.reduction X n).obj K))
      (WH : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
        ((d.reduction X n).obj H)) (k : K ⟶ H),
  (d.completedPull g).map ((d.push f).map k) ≫ d.completedBaseChangeMap sq H hH WH =
        d.completedBaseChangeMap sq K _hK WK ≫
          (d.push f').map ((d.completedPull g').map k)) ∧
  (∀  {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
      (sq : ChosenCartesianSquare (𝟙 X) f f (𝟙 Y))
      (K : d.derived X) (_hK : d.TowerComplete X K)
      (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
        ((d.reduction X n).obj K)),
  d.completedBaseChangeMap sq K _hK W =
        (d.completedPullId Y ((d.push f).obj K) (d.push_complete f K _hK)).hom ≫
          (d.push f).map (d.completedPullId X K _hK).inv) ∧
  (∀  {X X' X'' Y Y' Y'' : Scheme.{u}}
      {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
      {g : Y' ⟶ Y} {g' : X' ⟶ X} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'}
      [IsProper f]
      (sq₁ : ChosenCartesianSquare g' f' f g)
      (sq₂ : ChosenCartesianSquare h' f'' f' h)
      (outer : ChosenCartesianSquare (h' ≫ g') f'' f (h ≫ g))
      (K : d.derived X) (_hK : d.TowerComplete X K)
      (_W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
        ((d.reduction X n).obj K)),
  d.completedExchange outer K =
        (d.completedPullComp h g).hom.app ((d.push f).obj K) ≫
          (d.completedPull h).map (d.completedExchange sq₁ K) ≫
            d.completedExchange sq₂ ((d.completedPull g').obj K) ≫
              (d.push f'').map ((d.completedPullComp h' g').inv.app K)) ∧
  (∀  {X X' Y Y' Z Z' : Scheme.{u}}
      {f : X ⟶ Y} {f' : X' ⟶ Y'} {e : Y ⟶ Z} {e' : Y' ⟶ Z'}
      {g' : X' ⟶ X} {g : Y' ⟶ Y} {k : Z' ⟶ Z}
      [IsProper f] [IsProper e]
      (sq₁ : ChosenCartesianSquare g' f' f g)
      (sq₂ : ChosenCartesianSquare g e' e k)
      (outer : ChosenCartesianSquare g' (f' ≫ e') (f ≫ e) k)
      (K : d.derived X) (_hK : d.TowerComplete X K)
      (_W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
        ((d.reduction X n).obj K)),
  d.completedExchange outer K =
        (d.completedPull k).map ((d.pushComp f e).inv.app K) ≫
          d.completedExchange sq₂ ((d.push f).obj K) ≫
            (d.push e').map (d.completedExchange sq₁ K) ≫
              (d.pushComp f' e').hom.app ((d.completedPull g').obj K))

/-- Units, both pasting equations, and refinement compatibility for the actual
completed proper/open exchange. All finite-origin and completeness conditions are retained.
Source: fix-lem-exchanges, clauses (2) and (4)
(blueprint: fix-lem-exchanges). -/
@[irreducible] def CompletedSupportExchangeLaws {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : Prop :=
  (∀  {X Y : Scheme.{u}} {f : X ⟶ Y}
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c : Compactification f)
      (sp : ChosenCartesianSquare (𝟙 c.Z) c.g c.g (𝟙 Y))
      (sj : OpenImmersionSquare (𝟙 X) c.i c.i (𝟙 c.Z))
      (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
      (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
      (_origins : PbcHasCompatibleEtaleOrigins X d K.obj),
  ∃ (_hK : d.TowerComplete X K.obj)
        (hF : d.TowerComplete Y ((cbcSupport d c).obj K.obj)),
        cbcExchange d c c (𝟙 c.Z) sp sj r a ha K ≫
            (cbcSupport d c).map (d.completedPullId X K.obj _hK).hom =
          (d.completedPullId Y ((cbcSupport d c).obj K.obj) hF).hom) ∧
  (∀  {X X' X'' Y Y' Y'' : Scheme.{u}}
      {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
      {g : Y' ⟶ Y} {g' : X' ⟶ X} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'}
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c : Compactification f) (c' : Compactification f') (c'' : Compactification f'')
      (gb : c'.Z ⟶ c.Z) (hb : c''.Z ⟶ c'.Z)
      (sp₁ : ChosenCartesianSquare gb c'.g c.g g)
      (sj₁ : OpenImmersionSquare g' c'.i c.i gb)
      (sp₂ : ChosenCartesianSquare hb c''.g c'.g h)
      (sj₂ : OpenImmersionSquare h' c''.i c'.i hb)
      (sp : ChosenCartesianSquare (hb ≫ gb) c''.g c.g (h ≫ g))
      (sj : OpenImmersionSquare (h' ≫ g') c''.i c.i (hb ≫ gb))
      (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
      (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
      (_origins : PbcHasCompatibleEtaleOrigins X d K.obj),
  ∃ _hK' : cbcCompleteProperty d X' r a ha ((d.completedPull g').obj K.obj),
        cbcExchange d c c'' (hb ≫ gb) sp sj r a ha K =
          (d.completedPullComp h g).hom.app ((cbcSupport d c).obj K.obj) ≫
            (d.completedPull h).map (cbcExchange d c c' gb sp₁ sj₁ r a ha K) ≫
            cbcExchange d (qf := cbcBaseChangeQuasiCompact c c' gb sj₁)
              c' c'' hb sp₂ sj₂ r a ha ⟨(d.completedPull g').obj K.obj, _hK'⟩ ≫
            (cbcSupport d c'').map ((d.completedPullComp h' g').inv.app K.obj)) ∧
  (∀  {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {g : Y' ⟶ Y} {g' : X' ⟶ X}
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c₁ c₂ : Compactification f) (c₁' c₂' : Compactification f')
      (gb₁ : c₁'.Z ⟶ c₁.Z) (gb₂ : c₂'.Z ⟶ c₂.Z)
      (sp₁ : ChosenCartesianSquare gb₁ c₁'.g c₁.g g)
      (sj₁ : OpenImmersionSquare g' c₁'.i c₁.i gb₁)
      (sp₂ : ChosenCartesianSquare gb₂ c₂'.g c₂.g g)
      (sj₂ : OpenImmersionSquare g' c₂'.i c₂.i gb₂)
      (u : c₁.Refinement c₂) (u' : c₁'.Refinement c₂')
      (_hu : u'.hom ≫ gb₂ = gb₁ ≫ u.hom)
      (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
      (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
      (_origins : PbcHasCompatibleEtaleOrigins X d K.obj),
  (d.completedPull g).map (cbcRefinementMap d u K.obj) ≫
          cbcExchange d c₁ c₁' gb₁ sp₁ sj₁ r a ha K =
        cbcExchange d c₂ c₂' gb₂ sp₂ sj₂ r a ha K ≫
          cbcRefinementMap d (qf := cbcBaseChangeQuasiCompact c₁ c₁' gb₁ sj₁)
            u' ((d.completedPull g').obj K.obj)) ∧
  (∀  {X Y : Scheme.{u}} {f : X ⟶ Y}
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
      (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
      (origins : PbcHasCompatibleEtaleOrigins X d K.obj),
  (∀ (c₁ c₂ : Compactification f) (u : c₁.Refinement c₂)
        (H : (cbcCompleteProperty d X r a ha).FullSubcategory) (k : K.obj ⟶ H.obj),
        (cbcSupport d c₂).map k ≫ cbcRefinementMap d u H.obj =
          cbcRefinementMap d u K.obj ≫ (cbcSupport d c₁).map k) ∧
      (∀ c : Compactification f,
        cbcRefinementMap d (Compactification.Refinement.id c) K.obj = 𝟙 _) ∧
      (∀ (c₁ c₂ c₃ : Compactification f) (u : c₁.Refinement c₂) (v : c₂.Refinement c₃),
        cbcRefinementMap d (u.comp v) K.obj =
          cbcRefinementMap d v K.obj ≫ cbcRefinementMap d u K.obj) ∧
      (∀ (c₀ c₀' c₁ c₂ : Compactification f)
        (u₁ : c₀.Refinement c₁) (u₂ : c₀.Refinement c₂)
        (v₁ : c₀'.Refinement c₁) (v₂ : c₀'.Refinement c₂),
        cbcCompactificationComparison d u₁ u₂ r a ha K origins =
          cbcCompactificationComparison d v₁ v₂ r a ha K origins) ∧
      (∀ (c₀ c₁ c₂ c₃ : Compactification f)
        (u₁ : c₀.Refinement c₁) (u₂ : c₀.Refinement c₂) (u₃ : c₀.Refinement c₃),
        cbcCompactificationComparison d u₁ u₂ r a ha K origins ≪≫
            cbcCompactificationComparison d u₂ u₃ r a ha K origins =
          cbcCompactificationComparison d u₁ u₃ r a ha K origins)) ∧
  (∀  {X X' Y Y' Z Z' : Scheme.{u}}
      {f : X ⟶ Y} {f' : X' ⟶ Y'} {h : Y ⟶ Z} {h' : Y' ⟶ Z'}
      {gx : X' ⟶ X} {gy : Y' ⟶ Y} {gz : Z' ⟶ Z}
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (cf : Compactification f) (ch : Compactification h)
      (chf : Compactification (f ≫ h))
      (cf' : Compactification f') (ch' : Compactification h')
      (chf' : Compactification (f' ≫ h'))
      (gbf : cf'.Z ⟶ cf.Z) (gbh : ch'.Z ⟶ ch.Z) (gbhf : chf'.Z ⟶ chf.Z)
      (spf : ChosenCartesianSquare gbf cf'.g cf.g gy)
      (sjf : OpenImmersionSquare gx cf'.i cf.i gbf)
      (sph : ChosenCartesianSquare gbh ch'.g ch.g gz)
      (sjh : OpenImmersionSquare gy ch'.i ch.i gbh)
      (sphf : ChosenCartesianSquare gbhf chf'.g chf.g gz)
      (sjhf : OpenImmersionSquare gx chf'.i chf.i gbhf)
      (b : cf.Z ⟶ chf.Z) (p : chf.Z ⟶ ch.Z)
      (b' : cf'.Z ⟶ chf'.Z) (p' : chf'.Z ⟶ ch'.Z)
      [IsProper p]
      [IsProper p']
      (hb : cf.i ≫ b = chf.i) (hp : b ≫ p = cf.g ≫ ch.i)
      (hq : p ≫ ch.g = chf.g)
      (hb' : cf'.i ≫ b' = chf'.i) (hp' : b' ≫ p' = cf'.g ≫ ch'.i)
      (hq' : p' ≫ ch'.g = chf'.g)
      (sq : IsPullback b cf.g p ch.i) (sq' : IsPullback b' cf'.g p' ch'.i)
      (_wb : b' ≫ gbhf = gbf ≫ b) (_wp : p' ≫ gbh = gbhf ≫ p)
      (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
      (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
      (_origins : PbcHasCompatibleEtaleOrigins X d K.obj),
  IsIso (cbcTowerCompositionMap d cf ch chf b p hb hp hq sq K.obj) ∧
      IsIso (cbcTowerCompositionMap d
        (qh := cbcBaseChangeQuasiCompact ch ch' gbh sjh)
        cf' ch' chf' b' p' hb' hp' hq' sq' ((d.completedPull gx).obj K.obj)) ∧
      ∃ hF : cbcCompleteProperty d Y r a ha ((cbcSupport d cf).obj K.obj),
        (d.completedPull gz).map (cbcTowerCompositionMap d cf ch chf b p hb hp hq sq K.obj) ≫
            cbcExchange d chf chf' gbhf sphf sjhf r a ha K =
          cbcExchange d ch ch' gbh sph sjh r a ha ⟨(cbcSupport d cf).obj K.obj, hF⟩ ≫
            (cbcSupport d ch').map (cbcExchange d cf cf' gbf spf sjf r a ha K) ≫
            cbcTowerCompositionMap d
              (qh := cbcBaseChangeQuasiCompact ch ch' gbh sjh)
              cf' ch' chf' b' p' hb' hp' hq' sq' ((d.completedPull gx).obj K.obj)) ∧
  (∀  {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (cf₁ cf₂ : Compactification f) (ch₁ ch₂ : Compactification h)
      (chf₁ chf₂ : Compactification (f ≫ h))
      (b₁ : cf₁.Z ⟶ chf₁.Z) (p₁ : chf₁.Z ⟶ ch₁.Z)
      (b₂ : cf₂.Z ⟶ chf₂.Z) (p₂ : chf₂.Z ⟶ ch₂.Z)
      [IsProper p₁]
      [IsProper p₂]
      (hb₁ : cf₁.i ≫ b₁ = chf₁.i) (hp₁ : b₁ ≫ p₁ = cf₁.g ≫ ch₁.i)
      (hq₁ : p₁ ≫ ch₁.g = chf₁.g)
      (hb₂ : cf₂.i ≫ b₂ = chf₂.i) (hp₂ : b₂ ≫ p₂ = cf₂.g ≫ ch₂.i)
      (hq₂ : p₂ ≫ ch₂.g = chf₂.g)
      (sq₁ : IsPullback b₁ cf₁.g p₁ ch₁.i) (sq₂ : IsPullback b₂ cf₂.g p₂ ch₂.i)
      (uf : cf₁.Refinement cf₂) (uh : ch₁.Refinement ch₂) (uhf : chf₁.Refinement chf₂)
      (_wb : uf.hom ≫ b₂ = b₁ ≫ uhf.hom) (_wp : uhf.hom ≫ p₂ = p₁ ≫ uh.hom)
      (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
      (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
      (_origins : PbcHasCompatibleEtaleOrigins X d K.obj),
  cbcTowerCompositionMap d cf₂ ch₂ chf₂ b₂ p₂ hb₂ hp₂ hq₂ sq₂ K.obj ≫
          cbcRefinementMap d uhf K.obj =
        (cbcSupport d ch₂).map (cbcRefinementMap d uf K.obj) ≫
          cbcRefinementMap d uh ((cbcSupport d cf₁).obj K.obj) ≫
            cbcTowerCompositionMap d cf₁ ch₁ chf₁ b₁ p₁ hb₁ hp₁ hq₁ sq₁ K.obj)

/-- The smooth-base-change conclusion for the specified finite-stage ordinary exchange.
Source: blueprint fix-lem-exchanges, clauses (1)--(4)
(blueprint: fix-lem-exchanges). -/
@[irreducible] def exchangeFiniteProetaleSmooth (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] : Prop :=
  ∀ [TopologicalSpace Λ] [DiscreteTopology Λ] {S T Y X : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y
      ⟶ T} {h : Y ⟶ X}
      [IsNoetherian X] [IsNoetherian Y] [IsNoetherian S] [IsNoetherian T]
      [Smooth p] [QuasiCompact g] [QuasiSeparated g]
      (sq : ChosenCartesianSquare h e p g) (N : ℕ)
      (_hcoeff : Etale.IsSmoothBaseChangeCoefficients N Λ S)
      (K : ProEtale.FiniteCoefficientDerivedCategory T Λ)
      (_hK : ProEtale.isBoundedConstructibleFiniteCoefficient T Λ K),
  IsIso ((ProEtale.finiteCoefficientRealization X Λ).mapDerivedCategory.map
        ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq.flip).app
          ((ProEtale.finiteCoefficientRealization T Λ).mapDerivedCategory.asEquivalence.inverse.obj
      K))) ∧
      ∀ (L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
        (_hL : Etale.DerivedCategory.isBoundedConstructible Λ T (DerivedCategory.Plus.ι.obj L))
        (α : (ProEtale.finiteCoefficientDerivedComparison T Λ).obj (DerivedCategory.Plus.ι.obj L) ≅
      K),
        (ProEtale.finiteCoefficientRealization X Λ).mapDerivedCategory.map
            ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq.flip).app
              ((ProEtale.finiteCoefficientRealization T
      Λ).mapDerivedCategory.asEquivalence.inverse.obj K)) =
          (ProEtale.finiteCoefficientRealization X Λ).mapDerivedCategory.map
            (((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor ⋙
                (ProEtale.upperStar (ModuleCat.{u + 1} Λ) p).leftDerivedFunctor).map
                  (ProEtale.finiteSmoothModelCoordinates Λ T K L α).inv ≫
              (ProEtale.baseChangeSourceComparisonIso g p Λ).inv.app L ≫
              (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
                (DerivedCategory.Plus.ι.map
                  ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq.flip).app L)) ≫
              (ProEtale.finiteSmoothTargetComparison Λ sq).hom.app L ≫
              ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) e).leftDerivedFunctor ⋙
                (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) h).rightDerivedFunctor).map
                  (ProEtale.finiteSmoothModelCoordinates Λ T K L α).hom)

/-- Smooth invertibility of the item's canonical completed mate, retaining its origins, lattice, and
conditional uniform-interval constructible landing.
Source: fix-lem-exchanges, clause (3)
(blueprint: fix-lem-exchanges). -/
@[irreducible] def exchangeIntegralSmooth (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra
      (Padic l) E] [FiniteDimensional (Padic l) E] : Prop :=
  ∀  {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
      (sq : ChosenCartesianSquare h e f g)
      [IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
      [Smooth f] [QuasiCompact g] [QuasiSeparated g]
      (_hT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
      (_hl : IsUnit (l : Γ(S, ⊤)))
      (_horder : ∀ n : ℕ,
        IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(S, ⊤)) ∧
        IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(X, ⊤)) ∧
        IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(T, ⊤)) ∧
        IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(Y, ⊤)))
      (K : PbcIntegralConstructible l E T)
      (_horigin : ∀ n : ℕ,
        ∃ L : Etale.BoundedConstructibleDerivedCategory
            (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) T,
          Nonempty ((pbcDerivedFunctionRealization T (pbcIntegralDatum l E) n).obj
            ((ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1}
                (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)) T).mapDerivedCategory.obj L.obj) ≅
            (sbcReduction l E T n).obj K.obj)),
  IsIso (sbcExchangeApp l E sq ((pbcConstructibleInclusion l E T).obj K)) ∧
      ((∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞)) →
        (∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ, ∀ i : ℤ,
          (IsConstructibleProEtaleCoefficientModuleSheaf S
            (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
            (sbcAdicFiniteCohomology l E S n
            ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj K.obj)) i) ∧
          ((i < a ∨ b < i) → IsZero
            (sbcAdicFiniteCohomology l E S n
            ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj K.obj)) i))) ∧
          (IsConstructibleProEtaleCoefficientModuleSheaf X
            (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
            (sbcAdicFiniteCohomology l E X n
            ((sbcFinitePull l E f n).obj
              ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj K.obj))) i) ∧
          ((i < a ∨ b < i) → IsZero
            (sbcAdicFiniteCohomology l E X n
            ((sbcFinitePull l E f n).obj
              ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj K.obj))) i))) ∧
          (IsConstructibleProEtaleCoefficientModuleSheaf Y
            (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
            (sbcAdicFiniteCohomology l E Y n
            ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj K.obj)) i) ∧
          ((i < a ∨ b < i) → IsZero
            (sbcAdicFiniteCohomology l E Y n
            ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj K.obj)) i))) ∧
          (IsConstructibleProEtaleCoefficientModuleSheaf X
            (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
            (sbcAdicFiniteCohomology l E X n
            ((sbcFinitePush l E h n).obj
              ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj K.obj))) i) ∧
          ((i < a ∨ b < i) → IsZero
            (sbcAdicFiniteCohomology l E X n
            ((sbcFinitePush l E h n).obj
              ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj K.obj))) i)))) →
        ∃ (hB : PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
            ((sbcPull l E f).obj ((sbcPush l E g).obj
              ((pbcConstructibleInclusion l E T).obj K))).obj)
          (hD : PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
            ((sbcPush l E h).obj ((sbcPull l E e).obj
              ((pbcConstructibleInclusion l E T).obj K))).obj),
          IsIso (ObjectProperty.homMk
            (P := PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E))
            (X := ⟨((sbcPull l E f).obj ((sbcPush l E g).obj
              ((pbcConstructibleInclusion l E T).obj K))).obj, hB⟩)
            (Y := ⟨((sbcPush l E h).obj ((sbcPull l E e).obj
              ((pbcConstructibleInclusion l E T).obj K))).obj, hD⟩)
            (sbcExchangeApp l E sq ((pbcConstructibleInclusion l E T).obj K)).hom))

/-- Smooth invertibility of the item's canonical raw localized mate, retaining its origins,
      lattice, and
conditional uniform-interval constructible landing.
Source: fix-lem-exchanges, clause (3)
(blueprint: fix-lem-exchanges). -/
@[irreducible] def exchangeRationalSmooth (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra
      (Padic l) E] [FiniteDimensional (Padic l) E] : Prop :=
  ∀ {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T} (sq :
      ChosenCartesianSquare h e f g) [IsNoetherian X] [IsNoetherian S] [IsNoetherian T]
      [IsNoetherian Y]
      [Smooth f] [QuasiCompact g] [QuasiSeparated g]
      (_hX : ∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞))
      (_hT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
      (_hl : IsUnit (l : Γ(S, ⊤)))
      (K : PbcRationalConstructible l E T)
      (L : IntegralLattice l E T _hT (sbcPrimeUnitOnSource l g _hl) K)
      (_hL : L.IsFiniteLevelEtaleAdmissible l E T _hT (sbcPrimeUnitOnSource l g _hl)),
  IsIso ((sbcRationalExchange l E sq).app ((pbcRationalInclusion l E T).obj K)) ∧
      (sbcTransportedExchange l E sq _hT (sbcPrimeUnitOnSource l g _hl) L =
        (sbcRationalExchange l E sq).app ((pbcRationalInclusion l E T).obj K)) ∧
      (∀ L' : IntegralLattice l E T _hT (sbcPrimeUnitOnSource l g _hl) K,
        L'.IsFiniteLevelEtaleAdmissible l E T _hT (sbcPrimeUnitOnSource l g _hl) →
        sbcTransportedExchange l E sq _hT (sbcPrimeUnitOnSource l g _hl) L' =
          sbcTransportedExchange l E sq _hT (sbcPrimeUnitOnSource l g _hl) L) ∧
      (L.IsSquareConstructiblyAdmissible l E T _hT (sbcPrimeUnitOnSource l g _hl) sq →
        SbcConstructibleExchangeRepresentation l E sq _hT (sbcPrimeUnitOnSource l g _hl) L)

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

/-- The specified common-stage exchange on one square, retaining all
admissible-lattice and common-overfield qualifications.
Source: fix-lem-exchanges, canonical common-stage normalization and clauses (1)--(3)
(blueprint: fix-lem-exchanges). -/
@[irreducible] def exchangeCommonStageSmoothAtSquare [Smooth f] [QuasiCompact g] [QuasiSeparated g]
    (hInvS : IsUnit (l : Γ(S, ⊤))) : Prop :=
  ∃ P : Presentation
        (iX := ⟨sbcPrimeUnitOnSource l f hInvS⟩)
        (iS := ⟨sbcPrimeUnitOnSource l (𝟙 S) hInvS⟩)
        (iT := ⟨sbcPrimeUnitOnSource l g hInvS⟩)
        (iY := ⟨sbcPrimeUnitOnSource l (e ≫ g) hInvS⟩) l Ω sq,
      (∀ (K : @pbcQbarCategory l _ Ω _ _ _ T _ dT
          ⟨sbcPrimeUnitOnSource l g hInvS⟩),
        (∃ (E : Padic.FiniteCoefficientFields l Ω)
          (J : pbcStageCategory l Ω T E)
          (L : IntegralLattice l (pbcFiniteField.{u} l Ω E) T dT.out
            (sbcPrimeUnitOnSource l g hInvS) J),
          L.IsFiniteLevelEtaleAdmissible l (pbcFiniteField.{u} l Ω E) T dT.out
            (sbcPrimeUnitOnSource l g hInvS) ∧
          Nonempty ((⟨E, J⟩ : @pbcQbarCategory l _ Ω _ _ _ T _ dT
            ⟨sbcPrimeUnitOnSource l g hInvS⟩) ≅ K) ∧
          (∀ (M : Padic.FiniteCoefficientFields l Ω) (a : E ≤ M),
            ∃ LM : IntegralLattice l (pbcFiniteField.{u} l Ω M) T dT.out
                (sbcPrimeUnitOnSource l g hInvS)
                (((pbcScalarSystem l Ω T dT.out (sbcPrimeUnitOnSource l g hInvS)).T a).obj
                  J),
              LM.IsFiniteLevelEtaleAdmissible l (pbcFiniteField.{u} l Ω M) T dT.out
                (sbcPrimeUnitOnSource l g hInvS))) →
        IsIso ((Presentation.exchange
          (iX := ⟨sbcPrimeUnitOnSource l f hInvS⟩)
          (iS := ⟨sbcPrimeUnitOnSource l (𝟙 S) hInvS⟩)
          (iT := ⟨sbcPrimeUnitOnSource l g hInvS⟩)
          (iY := ⟨sbcPrimeUnitOnSource l (e ≫ g) hInvS⟩) l Ω sq P).app K)) ∧
      (∀ (Q : (pbcAmbientCompleteSystem l Ω T
          (hInv := ⟨sbcPrimeUnitOnSource l g hInvS⟩)).PairCategory)
        (M : Padic.FiniteCoefficientFields l Ω) (a : Q.stage ≤ M),
        (StageSystem.Morphism.descNatTrans (Presentation.alpha
          (iX := ⟨sbcPrimeUnitOnSource l f hInvS⟩)
          (iS := ⟨sbcPrimeUnitOnSource l (𝟙 S) hInvS⟩)
          (iT := ⟨sbcPrimeUnitOnSource l g hInvS⟩)
          (iY := ⟨sbcPrimeUnitOnSource l (e ≫ g) hInvS⟩) P)).app Q =
          Presentation.atStage
            (iX := ⟨sbcPrimeUnitOnSource l f hInvS⟩)
            (iS := ⟨sbcPrimeUnitOnSource l (𝟙 S) hInvS⟩)
            (iT := ⟨sbcPrimeUnitOnSource l g hInvS⟩)
            (iY := ⟨sbcPrimeUnitOnSource l (e ≫ g) hInvS⟩) l Ω sq P Q M a) ∧
      (∀ (E : Padic.FiniteCoefficientFields l Ω)
        (K : PbcRationalConstructible l (pbcFiniteField.{u} l Ω E) T)
        (L L' : IntegralLattice l (pbcFiniteField.{u} l Ω E) T dT.out
          (sbcPrimeUnitOnSource l g hInvS) K),
        L.IsFiniteLevelEtaleAdmissible l (pbcFiniteField.{u} l Ω E) T dT.out
          (sbcPrimeUnitOnSource l g hInvS) →
        L'.IsFiniteLevelEtaleAdmissible l (pbcFiniteField.{u} l Ω E) T dT.out
          (sbcPrimeUnitOnSource l g hInvS) →
        sbcTransportedExchange l (pbcFiniteField.{u} l Ω E) sq dT.out
            (sbcPrimeUnitOnSource l g hInvS) L =
          sbcTransportedExchange l (pbcFiniteField.{u} l Ω E) sq dT.out
            (sbcPrimeUnitOnSource l g hInvS) L')

end

/-- The common-stage exchange clause, universally quantified over its precise domain.
Source: fix-lem-exchanges, canonical common-stage normalization and clauses (1)--(3)
(blueprint: fix-lem-exchanges). -/
@[irreducible] def exchangeCommonStageSmooth (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] : Prop :=
  ∀ {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
  [IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
  [_dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [_dS : Fact (∃ n : ℕ, topologicalKrullDim S ≤ n)]
  [_dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [_dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  (sq : ChosenCartesianSquare h e f g) [Smooth f] [QuasiCompact g] [QuasiSeparated g]
    (hInvS : IsUnit (l : Γ(S, ⊤))),
    exchangeCommonStageSmoothAtSquare l Ω sq hInvS


/-- Identification of the canonical completed mate with its finite mates and its
strict derived-limit realization. This is about the same sbcExchangeApp as smooth invertibility.
Source: fix-lem-exchanges, construction and proof steps 4--5, 17--18
(blueprint: fix-lem-exchanges). -/
@[irreducible] def exchangeIntegralNormalization (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
      [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : Prop :=
  (∀ {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
    (sq : ChosenCartesianSquare h e f g) (K : PbcComplete l E T) (n : ℕ),
  (sbcReduction l E X n).map (sbcExchangeApp l E sq K).hom ≫
          sbcPushReduction l E h n ((sbcPull l E e).obj K) ≫
          (sbcFinitePush l E h n).map (sbcPullReduction l E e n K) =
        sbcPullReduction l E f n ((sbcPush l E g).obj K) ≫
          (sbcFinitePull l E f n).map (sbcPushReduction l E g n K) ≫
          sbcFiniteExchangeApp l E sq n ((sbcReduction l E T n).obj K.obj)) ∧
  (∀ {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
    (sq : ChosenCartesianSquare h e f g) (K : PbcComplete l E T),
  (sbcExchangeApp l E sq K).hom =
        (sbcStrictSourceComparison l E sq K).hom ≫
          (completedTowerRlim (pbcIntegralDatum l E) X).map
            (sbcStrictExchange l E sq K) ≫
          (sbcStrictTargetComparison l E sq K).hom)

/-- Identity, horizontal and vertical pasting, and the canonical compactification comparison for
      Ex_! at finite etale coefficients.
Source: blueprint fix-lem-exchanges, clauses (1)--(4)
(blueprint: fix-lem-exchanges). -/
@[irreducible] def exchangeFiniteSupportLaws (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] : Prop :=
  (∀ {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (hi : IsPullback (𝟙 X) c.i c.i (𝟙 c.Z))
      (hp : IsPullback (𝟙 c.Z) c.g c.g (𝟙 Y)),
  ((Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shriekBaseChange c c (𝟙 c.Z) hi hp).natTrans =
        Functor.whiskerLeft ((Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shriek c)
      ((Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).pbId Y).hom ≫ (Functor.rightUnitor _).hom
      ≫
          (Functor.leftUnitor _).inv ≫ Functor.whiskerRight ((Etale.derivedPlusFormalism
      (ModuleCat.{u + 1} Λ)).pbId X).inv ((Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shriek
      c)) ∧
  (∀ {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {X'' Y'' : Scheme.{u}} {f'' : X'' ⟶ Y''}
      {a' : X'' ⟶ X'}
      {a : Y'' ⟶ Y'} {b' : X' ⟶ X} {b : Y' ⟶ Y} (c : Compactification f)
      (c' : Compactification f') (c'' : Compactification f'') (h₁ : c''.Z ⟶ c'.Z)
      (h₂ : c'.Z ⟶ c.Z) (hi₁ : IsPullback a' c''.i c'.i h₁) (hp₁ : IsPullback h₁ c''.g c'.g a)
      (hi₂ : IsPullback b' c'.i c.i h₂) (hp₂ : IsPullback h₂ c'.g c.g b)
      (hi : IsPullback (a' ≫ b') c''.i c.i (h₁ ≫ h₂)) (hp : IsPullback (h₁ ≫ h₂) c''.g c.g (a ≫ b)),
  (Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shriekBaseChange c c'' (h₁ ≫ h₂) hi hp =
        (((Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shriekBaseChange c c' h₂ hi₂ hp₂ ≫ᵥ
      (Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shriekBaseChange c' c'' h₁ hi₁
      hp₁).whiskerLeft
          ((Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).pbComp' a' b' (a' ≫ b')
      rfl).inv).whiskerRight ((Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).pbComp' a b (a ≫
      b) rfl).hom) ∧
  (∀ {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
      [HasCompactification f] [HasCompactification f']
      [QuasiCompact f] [QuasiCompact f'] (sq : IsPullback g' f' f g) (c : Compactification f),
  (Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).lowerShriekBaseChange sq =
        (((Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shriekBaseChangeOfIsPullback sq
      c).whiskerTop
          ((Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shriekIso
      (HasCompactification.compactification f) c).hom).whiskerBottom
          ((Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shriekIso _
      (HasCompactification.compactification f')).hom) ∧
  (∀ {X X' Y Y' : Scheme.{u}} {S S' : Scheme.{u}} {f₁ : X ⟶ Y} {f₂ : Y ⟶ S}
      {f₁' : X' ⟶ Y'} {f₂' : Y' ⟶ S'} {gX : X' ⟶ X} {gY : Y' ⟶ Y} {gS : S' ⟶ S}
      [HasCompactification f₁] [HasCompactification f₂] [HasCompactification (f₁ ≫ f₂)]
      [HasCompactification f₁'] [HasCompactification f₂'] [HasCompactification (f₁' ≫ f₂')]
      [QuasiCompact (f₁ ≫ f₂)] [QuasiCompact f₁'] [QuasiCompact f₂'] [QuasiCompact (f₁' ≫ f₂')]
      (sq₁ : IsPullback gX f₁' f₁ gY) (sq₂ : IsPullback gY f₂' f₂ gS)
      (sq : IsPullback gX (f₁' ≫ f₂') (f₁ ≫ f₂) gS),
  (Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).lowerShriekBaseChange sq =
        (((Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).lowerShriekBaseChange sq₁ ≫ₕ
      (Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).lowerShriekBaseChange sq₂).whiskerTop
          ((Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).lowerShriekCompIso f₁
      f₂).inv).whiskerBottom ((Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).lowerShriekCompIso
      f₁' f₂').hom)

/-- The prescribed localized completed Ex_! component, and its identity and both pasting equations;
      all endpoint constructibility predicates are retained.
Source: blueprint fix-lem-exchanges, clauses (1)--(4)
(blueprint: fix-lem-exchanges). -/
@[irreducible] def exchangeRationalSupportLaws (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
      [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : Prop :=
  (∀ {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
      {f : X ⟶ Y} {g : Y' ⟶ Y} (c : Compactification f)
      (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
      (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
      (openSquare : OpenImmersionSquare g' c'.i c.i gbar)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
      (_dimX : ∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))
      (_dimY : ∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))
      (_dimX' : ∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))
      (_dimY' : ∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))
      (_hlX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
      (_hlY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
      (_hlX' : ∀ x' : X', IsUnit (l : X'.presheaf.stalk x'))
      (_hlY' : ∀ y' : Y', IsUnit (l : Y'.presheaf.stalk y')),
  ∃ (hSource : ∀ K : PbcBoundedConstructibleComplete X
          (pbcIntegralDatum l E),
        PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum l E)
          ((cbcCompactSupportSource g c (pbcIntegralDatum l E)).obj K.obj)),
        ∃ (hTarget : ∀ K : PbcBoundedConstructibleComplete X
          (pbcIntegralDatum l E),
        PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum l E)
          ((cbcCompactSupportTarget g' c' (pbcIntegralDatum l E)).obj K.obj)),
        ∃ η : LiftedCbc.cbcCompactSupportSourceTransport l E g c
            (pbcIntegralDatum l E) hSource ≅
          LiftedCbc.cbcCompactSupportTargetTransport l E g' c'
            (pbcIntegralDatum l E) hTarget,
          ∀ (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E))
            (r : ℕ) (a : Fin r → PbcIntegralRing l E)
            (ha : Ideal.span (Set.range a) = (pbcIntegralDatum l E).ideal)
            (hComplete : cbcCompleteProperty (pbcIntegralDatum l E) X r a ha K.obj),
            η.hom.app ⟨K⟩ =
              LiftedCbc.finiteExtensionCompactSupportExchangeComponent l E c c' gbar
                properSquare openSquare r a ha hSource hTarget K hComplete) ∧
  (∀ {X Y : Scheme.{u}} {f : X ⟶ Y}
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (_hX : CbcFiniteExtensionDomain l X) (_hY : CbcFiniteExtensionDomain l Y)
      (c : Compactification f)
      (sp : ChosenCartesianSquare (𝟙 c.Z) c.g c.g (𝟙 Y))
      (sj : OpenImmersionSquare (𝟙 X) c.i c.i (𝟙 c.Z))
      (r : ℕ) (a : Fin r → PbcIntegralRing l E)
      (ha : Ideal.span (Set.range a) = (pbcIntegralDatum l E).ideal)
      (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)),
  ∃ (_hK : (pbcIntegralDatum l E).TowerComplete X K.obj)
        (hF : (pbcIntegralDatum l E).TowerComplete Y
          ((cbcSupport (pbcIntegralDatum l E) c).obj K.obj))
        (hS : PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E)
          (((pbcIntegralDatum l E).completedPull (𝟙 Y)).obj
            ((cbcSupport (pbcIntegralDatum l E) c).obj K.obj)))
        (hT : PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E)
          ((cbcSupport (pbcIntegralDatum l E) c).obj K.obj)),
        LiftedCbc.finiteExtensionRationalArrow l E hS hT
          (cbcExchange (pbcIntegralDatum l E) c c (𝟙 c.Z) sp sj r a ha
              ⟨K.obj, LiftedCbc.finiteExtension_cbcComplete l E X K r a ha⟩ ≫
            (cbcSupport (pbcIntegralDatum l E) c).map
              ((pbcIntegralDatum l E).completedPullId X K.obj _hK).hom) =
        LiftedCbc.finiteExtensionRationalArrow l E hS hT
          ((pbcIntegralDatum l E).completedPullId Y
            ((cbcSupport (pbcIntegralDatum l E) c).obj K.obj) hF).hom) ∧
  (∀ {X X' X'' Y Y' Y'' : Scheme.{u}}
      {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
      {g : Y' ⟶ Y} {g' : X' ⟶ X} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'}
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (_hX : CbcFiniteExtensionDomain l X) (_hX' : CbcFiniteExtensionDomain l X')
      (_hX'' : CbcFiniteExtensionDomain l X'') (_hY : CbcFiniteExtensionDomain l Y)
      (_hY' : CbcFiniteExtensionDomain l Y') (_hY'' : CbcFiniteExtensionDomain l Y'')
      (c : Compactification f) (c' : Compactification f') (c'' : Compactification f'')
      (gb : c'.Z ⟶ c.Z) (hb : c''.Z ⟶ c'.Z)
      (sp₁ : ChosenCartesianSquare gb c'.g c.g g)
      (sj₁ : OpenImmersionSquare g' c'.i c.i gb)
      (sp₂ : ChosenCartesianSquare hb c''.g c'.g h)
      (sj₂ : OpenImmersionSquare h' c''.i c'.i hb)
      (sp : ChosenCartesianSquare (hb ≫ gb) c''.g c.g (h ≫ g))
      (sj : OpenImmersionSquare (h' ≫ g') c''.i c.i (hb ≫ gb))
      (r : ℕ) (a : Fin r → PbcIntegralRing l E)
      (ha : Ideal.span (Set.range a) = (pbcIntegralDatum l E).ideal)
      (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)),
  ∃ (_hK' : cbcCompleteProperty (pbcIntegralDatum l E) X' r a ha
          (((pbcIntegralDatum l E).completedPull g').obj K.obj))
        (hS : PbcIsBoundedConstructibleComplete Y'' (pbcIntegralDatum l E)
          (((pbcIntegralDatum l E).completedPull (h ≫ g)).obj
            ((cbcSupport (pbcIntegralDatum l E) c).obj K.obj)))
        (hT : PbcIsBoundedConstructibleComplete Y'' (pbcIntegralDatum l E)
          ((cbcSupport (pbcIntegralDatum l E) c'').obj
            (((pbcIntegralDatum l E).completedPull (h' ≫ g')).obj K.obj))),
        LiftedCbc.finiteExtensionRationalArrow l E hS hT
          (cbcExchange (pbcIntegralDatum l E) c c'' (hb ≫ gb) sp sj r a ha
            ⟨K.obj, LiftedCbc.finiteExtension_cbcComplete l E X K r a ha⟩) =
        LiftedCbc.finiteExtensionRationalArrow l E hS hT
          (((pbcIntegralDatum l E).completedPullComp h g).hom.app
              ((cbcSupport (pbcIntegralDatum l E) c).obj K.obj) ≫
            ((pbcIntegralDatum l E).completedPull h).map
              (cbcExchange (pbcIntegralDatum l E) c c' gb sp₁ sj₁ r a ha
                ⟨K.obj, LiftedCbc.finiteExtension_cbcComplete l E X K r a ha⟩) ≫
            cbcExchange (pbcIntegralDatum l E)
              (qf := cbcBaseChangeQuasiCompact c c' gb sj₁)
              c' c'' hb sp₂ sj₂ r a ha
              ⟨((pbcIntegralDatum l E).completedPull g').obj K.obj, _hK'⟩ ≫
            (cbcSupport (pbcIntegralDatum l E) c'').map
              (((pbcIntegralDatum l E).completedPullComp h' g').inv.app K.obj))) ∧
  (∀ {X X' Y Y' Z Z' : Scheme.{u}}
      {f : X ⟶ Y} {f' : X' ⟶ Y'} {h : Y ⟶ Z} {h' : Y' ⟶ Z'}
      {gx : X' ⟶ X} {gy : Y' ⟶ Y} {gz : Z' ⟶ Z}
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (_hX : CbcFiniteExtensionDomain l X) (_hX' : CbcFiniteExtensionDomain l X')
      (_hY : CbcFiniteExtensionDomain l Y) (_hY' : CbcFiniteExtensionDomain l Y')
      (_hZ : CbcFiniteExtensionDomain l Z) (_hZ' : CbcFiniteExtensionDomain l Z')
      (cf : Compactification f) (ch : Compactification h)
      (chf : Compactification (f ≫ h))
      (cf' : Compactification f') (ch' : Compactification h')
      (chf' : Compactification (f' ≫ h'))
      (gbf : cf'.Z ⟶ cf.Z) (gbh : ch'.Z ⟶ ch.Z) (gbhf : chf'.Z ⟶ chf.Z)
      (spf : ChosenCartesianSquare gbf cf'.g cf.g gy)
      (sjf : OpenImmersionSquare gx cf'.i cf.i gbf)
      (sph : ChosenCartesianSquare gbh ch'.g ch.g gz)
      (sjh : OpenImmersionSquare gy ch'.i ch.i gbh)
      (sphf : ChosenCartesianSquare gbhf chf'.g chf.g gz)
      (sjhf : OpenImmersionSquare gx chf'.i chf.i gbhf)
      (b : cf.Z ⟶ chf.Z) (p : chf.Z ⟶ ch.Z)
      (b' : cf'.Z ⟶ chf'.Z) (p' : chf'.Z ⟶ ch'.Z)
      [IsProper p] [IsProper p']
      (hb : cf.i ≫ b = chf.i) (hp : b ≫ p = cf.g ≫ ch.i)
      (hq : p ≫ ch.g = chf.g)
      (hb' : cf'.i ≫ b' = chf'.i) (hp' : b' ≫ p' = cf'.g ≫ ch'.i)
      (hq' : p' ≫ ch'.g = chf'.g)
      (sq : IsPullback b cf.g p ch.i) (sq' : IsPullback b' cf'.g p' ch'.i)
      (_wb : b' ≫ gbhf = gbf ≫ b) (_wp : p' ≫ gbh = gbhf ≫ p)
      (r : ℕ) (a : Fin r → PbcIntegralRing l E)
      (ha : Ideal.span (Set.range a) = (pbcIntegralDatum l E).ideal)
      (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)),
  ∃ (hF : cbcCompleteProperty (pbcIntegralDatum l E) Y r a ha
          ((cbcSupport (pbcIntegralDatum l E) cf).obj K.obj))
        (hS : PbcIsBoundedConstructibleComplete Z' (pbcIntegralDatum l E)
          (((pbcIntegralDatum l E).completedPull gz).obj
            ((cbcSupport (pbcIntegralDatum l E) ch).obj
              ((cbcSupport (pbcIntegralDatum l E) cf).obj K.obj))))
        (hT : PbcIsBoundedConstructibleComplete Z' (pbcIntegralDatum l E)
          ((cbcSupport (pbcIntegralDatum l E) chf').obj
            (((pbcIntegralDatum l E).completedPull gx).obj K.obj))),
        LiftedCbc.finiteExtensionRationalArrow l E hS hT
          (((pbcIntegralDatum l E).completedPull gz).map
              (cbcTowerCompositionMap (pbcIntegralDatum l E)
                cf ch chf b p hb hp hq sq K.obj) ≫
            cbcExchange (pbcIntegralDatum l E) chf chf' gbhf sphf sjhf r a ha
              ⟨K.obj, LiftedCbc.finiteExtension_cbcComplete l E X K r a ha⟩) =
        LiftedCbc.finiteExtensionRationalArrow l E hS hT
          (cbcExchange (pbcIntegralDatum l E) ch ch' gbh sph sjh r a ha
              ⟨(cbcSupport (pbcIntegralDatum l E) cf).obj K.obj, hF⟩ ≫
            (cbcSupport (pbcIntegralDatum l E) ch').map
              (cbcExchange (pbcIntegralDatum l E) cf cf' gbf spf sjf r a ha
                ⟨K.obj, LiftedCbc.finiteExtension_cbcComplete l E X K r a ha⟩) ≫
            cbcTowerCompositionMap (pbcIntegralDatum l E)
              (qh := cbcBaseChangeQuasiCompact ch ch' gbh sjh)
              cf' ch' chf' b' p' hb' hp' hq' sq'
              (((pbcIntegralDatum l E).completedPull gx).obj K.obj)))

/-- Transpose the chosen Cartesian diagram, retaining its actual pullback projections.
This changes only the square-label convention of the smooth-base-change modules.
Source: fix-lem-exchanges, clause (3), labels exchanged
(blueprint: fix-lem-exchanges). -/
def exchangeTransposeSquare {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) : ChosenCartesianSquare f' g' g f where
  w := sq.w.symm
  isoPullback := sq.isoPullback ≪≫ pullbackSymmetry f g
  hom_fst := by
    simp only [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact sq.hom_snd
  hom_snd := by
    simp only [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd]
    exact sq.hom_fst


/-- Smooth invertibility of the actual finite module Ex_*, and its canonical identification with
      the abelian smooth map after forgetting coefficients.
Source: blueprint fix-lem-exchanges, clauses (1)--(4)
(blueprint: fix-lem-exchanges). -/
@[irreducible] def exchangeFiniteModuleSmooth (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] : Prop :=
  ∀ {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} {g : Y' ⟶ Y} [Smooth g] [QuasiCompact f] [QuasiSeparated f]
    (sq : ChosenCartesianSquare g' f' f g) (N : ℕ)
    (_hcoeff : Etale.IsSmoothBaseChangeCoefficients N Λ Y)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K.obj),
    IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) ∧
    (D+(Etale.moduleAbelianForget Λ Y').map
        ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) ≫
      (Etale.moduleAbelianDerivedExchangeTargetIso Λ g' f' K).hom =
        (Etale.moduleAbelianDerivedExchangeSourceIso Λ f g K).hom ≫
          (Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
            (D+(Etale.moduleAbelianForget Λ X).obj K)) ∧
    (Etale.abelianDerivedBaseChangeArrow (exchangeTransposeSquare sq)
        ((D+(Etale.moduleAbelianForget Λ X).obj K).obj) =
      D(Etale.upperStar AddCommGrpCat.{u + 1} g).map
          ((Etale.lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlusCompatibility.inv.app
            (D+(Etale.moduleAbelianForget Λ X).obj K)) ≫
        _root_.DerivedCategory.Plus.ι.map
          ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
            (D+(Etale.moduleAbelianForget Λ X).obj K)) ≫
        (Etale.lowerStar AddCommGrpCat.{u + 1} f').rightDerivedFunctorPlusCompatibility.hom.app
          (D+(Etale.upperStar AddCommGrpCat.{u + 1} g').obj
            (D+(Etale.moduleAbelianForget Λ X).obj K)))

/-- Naturality of the same finite module Ex_* used in identity, pasting, and smoothness.
Source: blueprint fix-lem-exchanges, clauses (1)--(4)
(blueprint: fix-lem-exchanges). -/
@[irreducible] def exchangeFiniteNaturality (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] : Prop :=
  ∀ {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (K H : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (a : K ⟶ H),
    ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus ⋙
      (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus).map a ≫
        (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app H =
      (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K ≫
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) g').mapDerivedCategoryPlus ⋙
          (Etale.lowerStar (ModuleCat.{u + 1} Λ) f').rightDerivedFunctorPlus).map a

/-- Naturality of the actual completed proper/open Ex_! on complete inputs with compatible origins.
Source: blueprint fix-lem-exchanges, clauses (1)--(4)
(blueprint: fix-lem-exchanges). -/
@[irreducible] def exchangeCompletedSupportNaturality {A : Type (u + 1)} [CommRing A] (d :
      AdicCoefficientDatum A) : Prop :=
  ∀ {X' X Y' Y : Scheme.{u}}
      {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c : Compactification f) (c' : Compactification f')
      (gbar : c'.Z ⟶ c.Z)
      (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
      (openSquare : OpenImmersionSquare g' c'.i c.i gbar)
      (r : ℕ) (a : Fin r → A)
      (ha : Ideal.span (Set.range a) = d.ideal)
      (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
      (_origins : PbcHasCompatibleEtaleOrigins X d K.obj),
  ∀ (H : (cbcCompleteProperty d X r a ha).FullSubcategory)
          (k : K.obj ⟶ H.obj),
          (d.completedPull g).map
              ((d.push c.g).map
                ((cbcDerivedOpenShriek d c.i c.isOpenImmersion).map k)) ≫
              completedCompactSupportExchange d c c' gbar properSquare openSquare r a ha H =
            completedCompactSupportExchange d c c' gbar properSquare openSquare r a ha K ≫
              (d.push c'.g).map
                ((cbcDerivedOpenShriek d c'.i c'.isOpenImmersion).map
                  ((d.completedPull g').map k))

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

/-- The specified common-stage exchange on one square, retaining all
admissible-lattice and common-overfield qualifications.
Source: fix-lem-exchanges, canonical common-stage normalization and clauses (1)--(3)
(blueprint: fix-lem-exchanges). -/
@[irreducible] def exchangeCommonStageSupportLawsAtSquare [IsSeparated f] [LocallyOfFiniteType f]
    [IsNoetherian Y] [IsNoetherian X']
    (_dimY : ∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))
    (_dimX' : ∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))
    (_invY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (_invX' : ∀ x : X', IsUnit (l : X'.presheaf.stalk x)) : Prop :=
  Nonempty (CbcQbarExchangeModel l Ω c c' gbar properSquare openSquare) ∧
      ∀ D : CbcQbarExchangeModel l Ω c c' gbar properSquare openSquare,
      (∀ (K : pbcQbarCategory l Ω X) (M : Padic.FiniteCoefficientFields l Ω)
        (h : K.stage ≤ M),
        (StageSystem.Morphism.descNatTrans D.exchange).app K =
          StageSystem.PairCategory.mkHom
            (X := D.U.base.functor.obj K) (Y := D.V.base.functor.obj K) M h h
            ((D.U.base.β h).hom.app K.obj ≫
              (D.exchange.τ M).app
                (((pbcScalarSystem l Ω X dX.out iX.out).T h).obj K.obj) ≫
              (D.V.base.β h).inv.app K.obj)) ∧
      (∀ (K A B : pbcQbarCategory l Ω X) (α : A ≅ K) (β : B ≅ K),
        D.U.base.functor.map α.inv ≫
            (StageSystem.Morphism.descNatTrans D.exchange).app A ≫
            D.V.base.functor.map α.hom =
          D.U.base.functor.map β.inv ≫
            (StageSystem.Morphism.descNatTrans D.exchange).app B ≫
            D.V.base.functor.map β.hom)

end

/-- The common-stage exchange clause, universally quantified over its precise domain.
Source: fix-lem-exchanges, canonical common-stage normalization and clauses (1)--(3)
(blueprint: fix-lem-exchanges). -/
@[irreducible] def exchangeCommonStageSupportLaws (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] : Prop :=
  ∀ {X' X Y' Y : Scheme.{u}}
  {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
  (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
  (openSquare : OpenImmersionSquare g' c'.i c.i gbar)
  [QuasiCompact f]
  [IsNoetherian X] [IsNoetherian Y']
  [_dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [_iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [_dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
  [_iY' : Fact (∀ y : Y', IsUnit (l : Y'.presheaf.stalk y))] [IsSeparated f] [LocallyOfFiniteType f]
    [IsNoetherian Y] [IsNoetherian X']
    (_dimY : ∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))
    (_dimX' : ∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))
    (_invY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (_invX' : ∀ x : X', IsUnit (l : X'.presheaf.stalk x)),
    exchangeCommonStageSupportLawsAtSquare l Ω c c' gbar properSquare openSquare _dimY _dimX' _invY
      _invX'


/-- Compatibility of the actual completed ambient exchange and its raw rational localization with
      the fixed coefficient mates.
Source: blueprint fix-lem-exchanges, clauses (1)--(4)
(blueprint: fix-lem-exchanges). -/
@[irreducible] def exchangeScalarCompatibility (l : ℕ) [Fact l.Prime] : Prop :=
  (∀ (E F : Type u) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (i : E →ₐ[Padic l] F)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {a : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f a) ,
  pbcScalarExchangeLeft l E F i sq = pbcScalarExchangeRight l E F i sq) ∧
  (∀ (E F : Type u) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (i : E →ₐ[Padic l] F)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {a : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f a) (K : PbcCompletedDerived X
      (pbcIntegralDatum l E))
      (hL : PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum l F)
        ((pbcEmbeddingAmbientTensor l E F i Y').obj
          ((pbcActualCompletedPull a (pbcIntegralDatum l E)).obj
            ((pbcActualDerivedPush f (pbcIntegralDatum l E)).obj K))))
      (hR : PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum l F)
        ((pbcActualDerivedPush f' (pbcIntegralDatum l F)).obj
          ((pbcActualCompletedPull g' (pbcIntegralDatum l F)).obj
            ((pbcEmbeddingAmbientTensor l E F i X).obj K)))),
  (pbcRationalization Y' (pbcIntegralDatum l F) (pbcUniformizer l F)).map
        (ObjectProperty.homMk (X := ⟨_, hL⟩) (Y := ⟨_, hR⟩)
          ((pbcScalarExchangeLeft l E F i sq).app K)) =
      (pbcRationalization Y' (pbcIntegralDatum l F) (pbcUniformizer l F)).map
        (ObjectProperty.homMk (X := ⟨_, hL⟩) (Y := ⟨_, hR⟩)
          ((pbcScalarExchangeRight l E F i sq).app K)))

/-- The direct-image compositor conjugate to the prescribed completed pullback compositor.
Source: fix-lem-exchanges, clause (2), canonical composition comparisons
(blueprint: fix-lem-exchanges). -/
def exchangeCompletedPushComp (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sbcPush l E f ⋙ sbcPush l E g ≅ sbcPush l E (f ≫ g) :=
  conjugateIsoEquiv ((sbcAdjunction l E g).comp (sbcAdjunction l E f))
    (sbcAdjunction l E (f ≫ g)) (sbcPullComp l E g f).symm

/-- Identity and both pasting equations of the actual completed adjunction mate,
and their images under raw rational localization. The identity isomorphism is fixed by
its ordinary completion-unit equation; the other comparisons are the published sbcPullComp
and its adjunction conjugate. Thus these are laws of the very maps occurring in smoothness.
Source: fix-lem-exchanges, clauses (1)--(3), proof steps 4--9 and 16--19
(blueprint: fix-lem-exchanges). -/
@[irreducible] def exchangeCompletedMateLaws
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : Prop :=
  ∃ e : ∀ X : Scheme.{u}, sbcPull l E (𝟙 X) ≅ 𝟭 (PbcComplete l E X),
  (∀ (X : Scheme.{u}) (K : PbcComplete l E X),
    sbcCompletionUnit l E (𝟙 X) K.obj ≫ ((e X).hom.app K).hom =
      (sbcOrdinaryDerivedIso l E (𝟙 X)).inv.app K.obj ≫
        (pbcActualDerivedPullIdIso (pbcIntegralDatum l E) X).hom.app K.obj) ∧
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (sq : ChosenCartesianSquare f (𝟙 X) (𝟙 Y) f) (K : PbcComplete l E X),
    sbcExchangeApp l E sq K =
      (e Y).hom.app ((sbcPush l E f).obj K) ≫ (sbcPush l E f).map ((e X).inv.app K)) ∧
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (sq : ChosenCartesianSquare f (𝟙 X) (𝟙 Y) f) (K : PbcComplete l E X),
    (sbcRationalExchange l E sq).app ⟨K⟩ =
      (sbcCompleteRationalize l E Y).map
        ((e Y).hom.app ((sbcPush l E f).obj K) ≫
          (sbcPush l E f).map ((e X).inv.app K))) ∧
  (∀ {X S T Y Z V : Scheme.{u}}
      {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {b : Y ⟶ T}
      {k : Z ⟶ X} {a : V ⟶ Z} {c : V ⟶ Y}
      (sq₁ : ChosenCartesianSquare h b f g)
      (sq₂ : ChosenCartesianSquare a c k h)
      (outer : ChosenCartesianSquare a (c ≫ b) (k ≫ f) g)
      (K : PbcComplete l E T),
    sbcExchangeApp l E outer K =
      (sbcPullComp l E f k).inv.app ((sbcPush l E g).obj K) ≫
        (sbcPull l E k).map (sbcExchangeApp l E sq₁ K) ≫
          sbcExchangeApp l E sq₂ ((sbcPull l E b).obj K) ≫
            (sbcPush l E a).map ((sbcPullComp l E b c).hom.app K)) ∧
  (∀ {X S T Y Z V : Scheme.{u}}
      {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {b : Y ⟶ T}
      {k : Z ⟶ X} {a : V ⟶ Z} {c : V ⟶ Y}
      (sq₁ : ChosenCartesianSquare h b f g)
      (sq₂ : ChosenCartesianSquare a c k h)
      (outer : ChosenCartesianSquare a (c ≫ b) (k ≫ f) g)
      (K : PbcComplete l E T),
    (sbcRationalExchange l E outer).app ⟨K⟩ =
      (sbcCompleteRationalize l E Z).map
        ((sbcPullComp l E f k).inv.app ((sbcPush l E g).obj K) ≫
          (sbcPull l E k).map (sbcExchangeApp l E sq₁ K) ≫
            sbcExchangeApp l E sq₂ ((sbcPull l E b).obj K) ≫
              (sbcPush l E a).map ((sbcPullComp l E b c).hom.app K))) ∧
  (∀ {X S T Y W R : Scheme.{u}}
      {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {b : Y ⟶ T}
      {q : S ⟶ R} {k : W ⟶ R} {r : X ⟶ W}
      (sq₁ : ChosenCartesianSquare h b f g)
      (sq₂ : ChosenCartesianSquare r f k q)
      (outer : ChosenCartesianSquare (h ≫ r) b k (g ≫ q))
      (K : PbcComplete l E T),
    sbcExchangeApp l E outer K =
      (sbcPull l E k).map ((exchangeCompletedPushComp l E g q).inv.app K) ≫
        sbcExchangeApp l E sq₂ ((sbcPush l E g).obj K) ≫
          (sbcPush l E r).map (sbcExchangeApp l E sq₁ K) ≫
            (exchangeCompletedPushComp l E h r).hom.app ((sbcPull l E b).obj K)) ∧
  (∀ {X S T Y W R : Scheme.{u}}
      {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {b : Y ⟶ T}
      {q : S ⟶ R} {k : W ⟶ R} {r : X ⟶ W}
      (sq₁ : ChosenCartesianSquare h b f g)
      (sq₂ : ChosenCartesianSquare r f k q)
      (outer : ChosenCartesianSquare (h ≫ r) b k (g ≫ q))
      (K : PbcComplete l E T),
    (sbcRationalExchange l E outer).app ⟨K⟩ =
      (sbcCompleteRationalize l E W).map
        ((sbcPull l E k).map ((exchangeCompletedPushComp l E g q).inv.app K) ≫
          sbcExchangeApp l E sq₂ ((sbcPush l E g).obj K) ≫
            (sbcPush l E r).map (sbcExchangeApp l E sq₁ K) ≫
              (exchangeCompletedPushComp l E h r).hom.app ((sbcPull l E b).obj K))) ∧
  (∀ {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S}
      {h : Y ⟶ X} {b : Y ⟶ T} (sq : ChosenCartesianSquare h b f g)
      (K H : PbcComplete l E T) (a : K ⟶ H),
    (sbcPull l E f).map ((sbcPush l E g).map a) ≫ sbcExchangeApp l E sq H =
      sbcExchangeApp l E sq K ≫ (sbcPush l E h).map ((sbcPull l E b).map a)) ∧
  (∀ {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S}
      {h : Y ⟶ X} {b : Y ⟶ T} (sq : ChosenCartesianSquare h b f g)
      (K H : PbcRationalComplete l E T) (a : K ⟶ H),
    (sbcRationalLeft l E (f := f) (g := g)).map a ≫
        (sbcRationalExchange l E sq).app H =
      (sbcRationalExchange l E sq).app K ≫
        (sbcRationalRight l E (e := b) (h := h)).map a)

/-- The completed mate in smoothness is the actual ambient coefficient exchange,
conjugated by the published unit-normalized pull and push model comparisons.
This is the identification needed for the scalar-change equations to concern this Ex_*.
Source: fix-lem-exchanges, clauses (1) and (3), proof steps 4--5 and 17--18
(blueprint: fix-lem-exchanges). -/
@[irreducible] def exchangeIntegralModelIdentification
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : Prop :=
  ∀ {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S}
    {h : Y ⟶ X} {e : Y ⟶ T} (sq : ChosenCartesianSquare h e f g)
    (K : PbcComplete l E T),
    (sbcExchangeApp l E sq K).hom =
      (QbarCoefficientSmoothBaseChange.pullModel l E f).hom.app
          ((sbcPush l E g).obj K) ≫
        (pbcActualCompletedPull f (pbcIntegralDatum l E)).map
          ((QbarCoefficientSmoothBaseChange.pushModel l E g).hom.app K.obj) ≫
        (pbcActualCompletedExchange (pbcIntegralDatum l E)
          (exchangeTransposeSquare sq)).app K.obj ≫
        (pbcActualDerivedPush h (pbcIntegralDatum l E)).map
          ((QbarCoefficientSmoothBaseChange.pullModel l E e).inv.app K) ≫
        (QbarCoefficientSmoothBaseChange.pushModel l E h).inv.app
          ((sbcPull l E e).obj K).obj

/-- Naturality under pre- and post-comparison of the square defining this very
completed mate. The right hand side contains sbcExchangeApp itself.
Source: fix-lem-exchanges, clause (1); lem-weil-pbc-mate-whisker specialized to sbcTheta
(blueprint: fix-lem-exchanges). -/
@[irreducible] def exchangeCompletedSquareNaturality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : Prop :=
  ∀ {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S}
    {h : Y ⟶ X} {e : Y ⟶ T} (sq : ChosenCartesianSquare h e f g)
    (G : PbcComplete l E S ⥤ PbcComplete l E X)
    (H : PbcComplete l E T ⥤ PbcComplete l E Y)
    (σ : G ⟶ sbcPull l E f) (τ : sbcPull l E e ⟶ H) (K : PbcComplete l E T),
    (mateEquiv (sbcAdjunction l E g) (sbcAdjunction l E h)
      (((TwoSquare.mk _ _ _ _ (sbcTheta l E sq).hom).whiskerTop σ).whiskerBottom τ)).natTrans.app K
      =
        σ.app ((sbcPush l E g).obj K) ≫ sbcExchangeApp l E sq K ≫
          (sbcPush l E h).map (τ.app K)

/-- Identification of the finite compact exchange in the fixed coefficient
coordinates with the dependency's chosen-compactification proper/open map.
Source: fix-lem-exchanges, clause (1), def-cbc-exchange-map at the pro-etale finite stage
(blueprint: fix-lem-exchanges). -/
@[irreducible] def exchangeFiniteCompactIdentification
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) : Prop :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  ∀ {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (c : Compactification f),
    ProEtale.canonicalFiniteCoefficientCompactSupportExchange l E n hn sq c =
      ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))
        (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd) c

/-- The datum's actual finite exchanges are the canonical pro-etale stage maps,
transported by its prescribed intrinsic realization; these are definitional identifications.
Source: fix-lem-exchanges, clause (1); def-fix-six-functor-datum
(blueprint: fix-lem-exchanges). -/
@[irreducible] def exchangeDatumFiniteIdentification
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) : Prop :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  ∀ Q : SixFunctorCompactifiedSquare D,
    (S.finiteExchangeProjection Q).1 = Functor.whiskerRight
    (Functor.whiskerLeft
      ((intrinsicFiniteTorsionConstructible C.l E n hn Q.X.obj.left).ι ⋙
        (sixFunctorFiniteRealization D C E n hn Q.X).inverse)
      (AlgebraicGeometry.ProEtale.derivedBaseChangeMap
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
        Q.square.toCommSq))
    (sixFunctorFiniteRealization D C E n hn Q.Y').functor ∧
    (S.finiteExchangeProjection Q).2.1 = Functor.whiskerRight
      (Functor.whiskerLeft
        ((intrinsicFiniteTorsionConstructible C.l E n hn Q.X.obj.left).ι ⋙
          (sixFunctorFiniteRealization D C E n hn Q.X).inverse)
        (AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
          Q.square Q.compactification))
      (sixFunctorFiniteRealization D C E n hn Q.Y').functor 

/-- The five finite-stage clauses at the specified positive uniformizer quotient.
The local instance is the dependency's finiteness theorem, transported through ULift.
Source: fix-lem-exchanges, finite coefficient convention
(blueprint: fix-lem-exchanges). -/
@[irreducible] def exchangeFiniteStageLaws
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) : Prop :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  exchangeFiniteNaturality (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) ∧
  exchangeFiniteOrdinaryLaws (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) ∧
  exchangeFiniteSupportLaws (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) ∧
  exchangeFiniteModuleSmooth (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) ∧
  exchangeFiniteProetaleSmooth (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))

/-- The four exchange clauses for the named canonical stage maps.

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/fix-lem-exchanges.
(blueprint: fix-lem-exchanges).

Proof (twenty steps, following the node):

1. At finite etale coefficients construct ordinary exchange as the constant-module unit, square
   comparison and counit mate. Construct compact exchange as that mate for the proper factor,
   followed by direct image of the open base-change isomorphism (def-cbc-exchange-map). Each
   factor is natural, hence so are both composites.

2. Use lem-weil-pbc-transport-identifies-exchange and thm-cbc-finite-level-proetale to identify
   these actual maps on witnessed pro-etale inputs. Witness isomorphisms conjugate both endpoints.
   Finite-type morphisms are quasi-compact and separated morphisms are quasi-separated. Finite-
   type schemes over the finite field are Noetherian and finite-dimensional; Nagata supplies the
   required compactifications.

3. The coefficient integers are a DVR by lem-weil-l-adic-extension-integers-dvr. Multiplication by
   a positive uniformizer power gives a two-term free resolution of each quotient, so it is
   perfect. Finite quotients are killed by powers of ell. Apply lem-weil-pbc-constant-completion-
   equivalence to identify complete categories, reductions, units and limits.

4. Apply lem-pur-completed-coefficient-pushforward-comparison with the distinct primes from the
   datum. Its K-injective and limit normalization identifies direct images. The unit-preserving
   coefficient equivalence and lem-sp-completed-pullback-adjunction identify the completed
   adjunctions and their units and counits.

5. By lem-sp-completion-mate-comparison the completed mate is the strict tower mate conjugated by
   the stated endpoint comparisons. The strict-tower exchange-mate normalization identifies the
   actual proper factor of def-cbc-completed-exchange-map with this mate before evaluation at any
   finite level.

6. Use lem-sf-cbc-extension-zero-completion: the completed open extension is completion after open
   extension, with its strict finite reduction isomorphism and unit normalization. The ringed
   tower pushforward-limit comparison identifies its proper direct image with the ordered derived
   limit of the proper/open tower. This gives the completed compact formula without commuting
   ordinary open extension through infinite limits.

7. Apply lem-weil-pbc-mate-whisker to the square comparisons. Mate commutes with pre- and post-
   whiskering by its explicit formula. Substitute the unit and counit coefficient comparisons of
   lem-fix-operation-reduction and prop-weil-pbc-scalar-extension; for compact support substitute
   also the open comparison. Retain the finite-Tor qualification of quotient comparisons.

8. Use the normalized finite pullback composition formula on tensor generators. On three factors
   both associations multiply the same scalars. At completed coefficients use the stated direct-
   image comparisons and their adjunction conjugates. Associativity of composite hom-set
   bijections proves the identity and associativity normalizations.

9. Apply the horizontal, vertical, adjunction-change and identity clauses of lem-weil-pbc-mate-
   pasting. The adjunction conjugates are exactly the specified direct-image compositors. This
   yields the ordinary identity and both pasting equations; at finite etale level they are lem-
   weil-pbc-exchange-identity-pasting and sbc-lem-identity-and-base-change-composition.

10. For compact support start with the proper/open expression of def-cbc-exchange-map. Use the
   extension-by-zero identity and pasting formulas together with the ordinary formulas for the
   proper factor. Proper/open interchange puts the resulting factors in the same order, giving the
   compact identity and horizontal equation.

11. For a refinement fixing the open use its proper/open comparison, rather than an unjustified
   Cartesian base-change square. The proper/open comparison composition equation and direct-image
   compositor naturality identify the two candidate compact exchanges. Pass through a common
   refinement and use prop-compactification-coherence-detailed to deduce independence.

12. Use the finite-level compact-support composition law thm-sf-comp-composition. Substitute the
   proper and open exchanges in each composite. Proper/open interchange and associativity of
   direct-image comparison identify both words. Compatibility with refinement comparisons makes
   the result independent of all chosen compactifications.

13. For the completed compact equations apply the strict reduction construction to these finite
   identities. The normalized completed-open reductions and strict proper exchange identify all
   factors with their finite ones. Apply the ordered derived limit and the specified direct-
   image/limit comparisons; their unit and projection normalizations identify the resulting
   completed comparisons.

14. For completed compactification and composition comparisons use the normalized reconstruction
   of the same strict proper/open words, together with the strict tower proper/open calculus.
   Equality of finite projections gives equality of the strict diagrams and therefore of their
   derived-limit maps. This gives the completed refinement and composition equations.

15. The common-refinement description makes completed compactification comparisons independent of
   the common refinement. The finite composition associativity and unit equations pass through the
   normalized reconstruction. Consequently the completed vertical pasting comparison is precisely
   the composition comparison specified by the datum.

16. Localize the integral maps and comparisons linearly at the uniformizer. Localization preserves
   all displayed compositions and identities. The scalar extension equations identify these
   localized maps at every finite overfield; coherent common-stage descent then preserves the same
   equations, including equal fields.

17. When the base arrow g is smooth, exchange the square labels in sbc-def-base-change-map. The
   finite etale mate is the bounded-below smooth-base-change morphism. Apply sbc-thm-bounded-
   below-derived-smooth-base-change, then forget-coefficient reflection and the etale/pro-etale
   exchange comparison to get the witnessed finite pro-etale result.

18. At integral coefficients the coefficient quotient order is invertible because it is a power of
   ell and ell differs from the base characteristic. Each retained finite etale-origin witness
   permits finite smooth base change. The reduction comparison identifies these with reductions of
   the completed mate; completeness detects its invertibility. A common finite cohomology interval
   supplies constructible landing exactly as in sbc-thm-adic-smooth-base-change.

19. At E coefficients use the specified finite-level admissible lattice. Localize its invertible
   integral mate. Naturality under its rational presentation identifies this map with the
   canonical raw rational exchange and makes it independent of the chosen lattice. Retain the
   square-constructible uniform-interval hypothesis for constructible landing, as in sbc-thm-e-
   coefficient-smooth-base-change.

20. At algebraically closed coefficients choose the retained admissible finite-stage
   representative. The previous step applies at that stage and every required common finite
   overfield. The scalar compatibility equation identifies all resulting exchanges and their
   inverses after extension. Common-stage descent and naturality give the specified exchange,
   independence, and invertibility; the output corner is Y-prime.
-/
theorem exchangeFunctoriality
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) :
    exchangeDatumFiniteIdentification D C E n hn S ∧
    exchangeFiniteStageLaws C.l E n hn ∧
    exchangeFiniteCompactIdentification C.l E n hn ∧
    CompletedOrdinaryExchangeLaws (pbcIntegralDatum C.l E) ∧
    CompletedSupportExchangeLaws (pbcIntegralDatum C.l E) ∧
    exchangeCompletedSupportNaturality (pbcIntegralDatum C.l E) ∧
    exchangeRationalSupportLaws C.l E ∧
    exchangeCommonStageSupportLaws C.l C.Qbar ∧
    exchangeScalarCompatibility C.l ∧
    exchangeIntegralModelIdentification C.l E ∧
    exchangeCompletedMateLaws C.l E ∧
    exchangeCompletedSquareNaturality C.l E ∧
    coefficientOperationMateEquations.{u} ∧
    compactSupportScalarExtensionLaws.{u} ∧
    exchangeIntegralNormalization C.l E ∧
    exchangeIntegralSmooth C.l E ∧
    exchangeRationalSmooth C.l E ∧
    exchangeCommonStageSmooth C.l C.Qbar := by
  sorry

end WeilConjectures
