/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralPurityCoefficientChange.PurityCoefficientChangeData
import WeilConjectures.CategoryTheory.PurityCoefficientChangeTransposition
import WeilConjectures.AlgebraicGeometry.PurityTransport.PurityCoefficientChangeCoordinates
import WeilConjectures.AlgebraicGeometry.GeneralPurityTransport.GeneralTransportData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixNonfiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixPerfectExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteScalarProjectionCase
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateProjection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixCtf
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence
import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
import WeilConjectures.Compactification.BaseChange
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
import WeilConjectures.CategoryTheory.CompactObject
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingEtaleCompactGenerators
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalTowerCoefficients
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTrace
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1Triangle
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
import WeilConjectures.ZetaWeil.PodCtfAdjunctionData.PodCtfAdjunctions
import WeilConjectures.AlgebraicGeometry.PurityCoefficientChange.CondensedPurityCoefficientChange
import WeilConjectures.AlgebraicGeometry.GeneralPurityCoefficientChange.PurityCoefficientChangeData
import WeilConjectures.AlgebraicGeometry.GeneralPurityCoefficientChange.PurityCoefficientChangeModels
import WeilConjectures.AlgebraicGeometry.PurityTransport.PurityCoefficientChangePresentations
import WeilConjectures.AlgebraicGeometry.GeneralPurityCoefficientChange.PurityCoefficientChangeFrobenius
import WeilConjectures.AlgebraicGeometry.GeneralPurityCoefficientChange.PurityCoefficientChangePowerUnits
import WeilConjectures.CategoryTheory.PurityCoefficientChangeMonoidal
import WeilConjectures.AlgebraicGeometry.GeneralPurityCoefficientChange.PurityCoefficientChangeModelsOfFactorization

/-!
# Purity and the smooth trace under change of coefficients

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-setup/sec-the-purity-statement/sk-thm-purity-transport/
sk-thm-purity-transport-coefficient-change.md`, clauses (1)--(3) and the final
assertion, with its proof (blueprint: det-sp-purity-coefficient-change).

The base is a field `k` that is finite or algebraically closed, with `ringChar k`
prime and different from `ell` (the setting of def-sf-setting).
The adjunction family `A` is any family of explicit restricted adjunctions of
def-pur-general-transport-data (`GeneralTransportData`) that satisfies its
predicates `BrownComparison`, `ScalarCompatible` and `AffineNormalized`: these are
the normalizations of the explicit adjunction of det-sp-comparison-brown-explicit
(counit normalized by affine-line integration and transported along the listed
coefficient changes).  `γ` is computed by `rightAdjointUniq` against the published
Brown restriction, i.e. it is the unique counit-compatible comparison of
det-sp-comparison-brown-unique (the `∃! gamma` clause of `BrownComparison`), and
`Tr = ε ∘ Rf_!(γ)` is the transported counit.  The base-change and composition
predicates and the purity theorem `smooth_purity_transport` are not assumed and its
module is not imported: that theorem's proof (its Step 4) applies this statement.
The coefficient comparisons are the published ones: `b` is
`scalarCompactSupportMap` (proper/open mate), `c` is `scalarExceptionalBeta`
(transpose of `T(ε) ∘ b⁻¹`), and the source map is `sourceScalar` on the
`Coordinates` of `Sheaf.Paper.CondensedPurityCoefficientChange`.

The definitions below are those of
`PurityCoefficientChange.condensed_purity_coefficient_change`
(lem-pur-condensed-purity-coefficient-change), with the finite-field datum
`D` replaced by the general field `k`; `IdentityCoherent` omits the
compact-support identity clause, which constrains no coordinate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open AlgebraicGeometry.ProEtale.GeneralPurityTransport
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.GeneralPurityCoefficientChange
variable (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]

attribute [local irreducible] scalarSixChange instCategoryDerivedCategory
  MorphismProperty.instCategoryLocalization DerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

-- The smooth trace is the actual counit of the supplied explicit adjunction.
omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)] in
set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
-- Elaborating the native derived functor presentations needs this budget.
set_option maxHeartbeats 1000000 in
-- Elaborating the native derived functor presentations needs this budget.
set_option maxHeartbeats 1000000 in
-- Elaborating the native derived functor presentations needs this budget.
set_option maxHeartbeats 1000000 in
-- Elaborating the native derived functor presentations needs this budget.
private theorem listed_cases {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (ha : ListedScalarChange ell a) :
    IsListedScalarCoefficientMap ell a ∨ ∃ h : Λ = Λ', a = eqToHom h := by
  induction ha with
  | ofListed h => exact Or.inl h
  | identity Λ hΛ => exact Or.inr ⟨rfl, rfl⟩
  | comp a b ha hb iha ihb =>
    rcases iha with h | ⟨e, rfl⟩
    · rcases ihb with h' | ⟨f, rfl⟩
      · exact Or.inl (.comp h h')
      · left
        simpa only [Iso.refl_hom, Category.id_comp, eqToIso.hom] using
          IsListedScalarCoefficientMap.iso (Iso.refl _) (eqToIso f) h
    · rcases ihb with h' | ⟨f, rfl⟩
      · left
        simpa only [Iso.refl_hom, Category.comp_id, eqToIso.hom] using
          IsListedScalarCoefficientMap.iso (eqToIso e) (Iso.refl _) h'
      · exact Or.inr ⟨e.trans f, by simp only [eqToHom_trans]⟩

-- Coordinates are actual normalized constructions; no arbitrary existence witness is used.
omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)] in
private theorem coordinates_nonempty (A : AdjunctionFamily ell k)
    (hScalar : GeneralPurityTransport.ScalarCompatible ell k A) :
    Nonempty (PurityCoefficientChange.Coordinates.{u} ell) := by
  have hi : ∀ {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell),
      ListedScalarChange ell a → c.integralMap ell ≫ a.hom.hom = c'.integralMap ell := by
    intro c c' a ha
    rcases listed_cases ell a ha with hlisted | ⟨h, rfl⟩
    · exact (hScalar c c' a hlisted).1
    · rcases coefficient_eqToHom_listed_or_closure ell c c' h with hlisted | ⟨hc, hc'⟩
      · exact (hScalar c c' (eqToHom h) hlisted).1
      · subst c
        subst c'
        exact Category.comp_id _
  exact ⟨{ integral := hi
           line := fun a ha X ↦ (scalarLineCoordinates_nonempty ell a (hi a ha) X).some }⟩

set_option maxHeartbeats 1000000 in
-- Elaborating the native derived functor presentations needs this budget.
set_option maxHeartbeats 1000000 in
-- Elaborating the native derived functor presentations needs this budget.
set_option maxHeartbeats 1000000 in
-- Elaborating the native derived functor presentations needs this budget.
set_option maxHeartbeats 1000000 in
-- Elaborating the native derived functor presentations needs this budget.
set_option maxHeartbeats 1000000 in
-- Elaborating the native derived functor presentations needs this budget.
set_option maxHeartbeats 1000000 in
-- Elaborating the native derived functor presentations needs this budget.
end AlgebraicGeometry.ProEtale.GeneralPurityCoefficientChange

namespace AlgebraicGeometry.ProEtale

open GeneralPurityCoefficientChange

end AlgebraicGeometry.ProEtale
