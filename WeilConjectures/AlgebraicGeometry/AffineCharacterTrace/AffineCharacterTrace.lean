/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralPurityTransport.GeneralTransport
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
public import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSmoothTraceUnit
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTateBasis
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleLisseModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleExtensionIso
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
import Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSheafConeWitness
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantModelLocalResolution
import WeilConjectures.ProperBaseChange.IntegralLfpLocallyFreeResolution
import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement

import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.Shift
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
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
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Braided
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

/-! # The normalized affine trace and its arbitrary-field base change

Source: latest blueprint, sec-fourier-transform/
sk-lem-wft-character-integral/lem-fd-character-integral.md,
the zero-case trace and final arbitrary-base paragraph; smooth trace (10.24).
(blueprint: def-wft-affine-character-trace).

The reference map is the recorded smooth trace at the dual shifted root line.
Its source is identified by the actual evaluation map. For an arbitrary algebraically
closed extension, the definition uses inverse compact-support exchange and pullback of
this reference map. No invertibility of the resulting trace is assumed in its definition.

## Main definitions

* `negativeTate` and `sourceEvaluation` specify the shifted line and its evaluation.
* `referenceTrace` specializes the published general normalized smooth trace.
* `exchange` and `trace` construct its transport to the arbitrary base.

## Main statements

* `projection_smooth` and `affineSquare` give the coordinate geometry.
* `negativeTate_mem` and `sourceEvaluation_isIso` justify untwisting.
* `exchange_isIso` is the specified constant-complex compact-support exchange.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.AffineCharacterTrace
open CondensedRing PurityTransport

/-- The affine projection is smooth of relative dimension r, including the identity
at r=0. Source: lem-fd-character-integral, trivial vector bundle
(blueprint: def-wft-affine-character-trace).
Proof: successive affine-line projections are smooth of relative dimension one;
composition adds relative dimensions. The empty composite is the identity. -/
theorem projection_smooth (S : Scheme.{u}) (r : ℕ) :
    SmoothOfRelativeDimension r (affineTraceProjection S r) := by
  induction r with
  | zero =>
    change SmoothOfRelativeDimension 0 (𝟙 S)
    infer_instance
  | succ r ih =>
    have hLine : SmoothOfRelativeDimension 1
        (AffineSpace PUnit.{u + 1} (affineTraceTower S r) ↘ affineTraceTower S r) := by
      simpa only [Nat.card_unique] using
        AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (affineTraceTower S r)
    simpa only [affineTraceProjection, Nat.add_comm] using
      (smoothOfRelativeDimension_comp 1 r
        (AffineSpace PUnit.{u + 1} (affineTraceTower S r) ↘ affineTraceTower S r)
        (affineTraceProjection S r))

/-- The actual affine projection in the general smooth-trace domain.
Source: lem-fd-character-integral, zero case (blueprint: def-wft-affine-character-trace). -/
def datum (K : Type u) [Field K] (r : ℕ) : GeneralPurityTransport.SmoothDatum K := by
  let S := Spec (.of K)
  let f := affineTraceProjection S r
  letI : IsSeparated f := inferInstanceAs (IsSeparated (affineTraceProjection S r))
  letI : LocallyOfFiniteType f :=
    inferInstanceAs (LocallyOfFiniteType (affineTraceProjection S r))
  letI : QuasiCompact f := inferInstanceAs (QuasiCompact (affineTraceProjection S r))
  exact
    { X := Over.mk f
      Y := Over.mk (𝟙 S)
      xFinite := inferInstanceAs (LocallyOfFiniteType (affineTraceProjection S r))
      xQuasiCompact := inferInstanceAs (QuasiCompact (affineTraceProjection S r))
      xSeparated := inferInstanceAs (IsSeparated (affineTraceProjection S r))
      yFinite := inferInstanceAs (LocallyOfFiniteType (𝟙 S))
      yQuasiCompact := inferInstanceAs (QuasiCompact (𝟙 S))
      ySeparated := inferInstanceAs (IsSeparated (𝟙 S))
      map := f
      isOver := ⟨Category.comp_id f⟩
      dim := r
      smooth := projection_smooth S r
      compactification := HasCompactification.compactification f }

/-- The published compactification lower-shriek functor, with a named boundary
for composing the reference and base-change morphisms.
Source: det-def-sfb-module-derived-lower-shriek, unbounded derived functor
(blueprint: def-wft-affine-character-trace). -/
def compactPush (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) :=
  CondensedRing.rightDerivedLowerShriekOfCompactification Λ c

/-- The coefficient object Lambda(-r)[-2r] is the derived dual of the shifted
positive root-tower line, on the base point, not compact cohomology of a twist.
Source: sk-def-sp-tate-twist, powers and duals
(blueprint: def-wft-affine-character-trace). -/
def negativeTate (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    (S : Scheme.{u}) (r : ℕ) : c.derived ell S :=
  (ihom (c.derivedLine ell S r)).obj (𝟙_ _)

/-- The negative shifted Tate line is bounded constructible of finite Tor amplitude.
Source: sk-def-sp-tate-twist, locally free lines and duals
(blueprint: def-wft-affine-character-trace).
Proof: on the compatible-root cover the positive line is the rank-one free module
shifted by 2r. Its derived dual is the rank-one free module shifted by -2r.
Finite presentation, constructibility and finite Tor amplitude descend. -/
theorem negativeTate_mem (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    (S : Scheme.{u}) [∀ x : S, Invertible (ell : S.residueField x)] (r : ℕ) :
    property ell c S (negativeTate ell c S r) := by
  sorry

/-- Evaluation after the root-normalized pullback comparison. The braiding moves
the positive line to the left, its inverse pullback comparison and the tensorator
identify the source with the pullback of L tensor RHom(L,1), and evaluation and
the pullback unit give the result. Source: trace (10.24), untwisting its source
(blueprint: def-wft-affine-character-trace). -/
def sourceEvaluation (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (r : ℕ)
    (p : LinePullCoordinates ell c f) :
    (c.smoothSource ell f r).obj (negativeTate ell c Y r) ⟶ 𝟙_ _ :=
  letI := _root_.DerivedCategory.braidedCategory'
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj (c.obj ell) X))
  let F := (CondensedRing.upperStar (c.obj ell) f).leftDerivedFunctor
  let L := c.derivedLine ell Y r
  let N := negativeTate ell c Y r
  (β_ (F.obj N) (c.derivedLine ell X r)).hom ≫
    (p.derived ell r).inv ▷ F.obj N ≫
    (Functor.Monoidal.μIso F L N).hom ≫
    F.map ((ihom.ev L).app (𝟙_ _)) ≫
    (Functor.Monoidal.εIso F).inv

/-- The specified evaluation is invertible; this does not assert invertibility
of a trace or choose a new trace. Source: the locally free Tate line, and the
untwisting of (10.24) (blueprint: def-wft-affine-character-trace).
Proof: on a compatible-root cover evaluation is multiplication of a basis and
its dual, with opposite even shifts cancelling. The normalized pullback carries
the same root basis. Thus evaluation is the unit isomorphism locally and descends. -/
theorem sourceEvaluation_isIso (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] (r : ℕ)
    (p : LinePullCoordinates ell c f) : IsIso (sourceEvaluation ell c f r p) := by
  let _ := DerivedCategory.braidedCategory'
    (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj (c.obj ell) Y))
  let _ := DerivedCategory.braidedCategory'
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj (c.obj ell) X))
  let U := (DerivedCategory.singleFunctor _ 0).obj (c.line ell Y r)
  let e := (scalarChangeUnit (c.bundled ell) Y).app U
  have hU : IsInvertible U := by
    obtain ⟨M, ⟨a⟩, ⟨b⟩⟩ :=
      native_tateLine_isInvertible ell (c.bundled ell) c (Iso.refl _) Y r
    exact ⟨M, ⟨tensorIso e.symm (Iso.refl M) ≪≫ a⟩,
      ⟨tensorIso (Iso.refl M) e.symm ≪≫ b⟩⟩
  have hL : IsInvertible (c.derivedLine ell Y r) := by
    obtain ⟨M, ⟨a⟩, ⟨b⟩⟩ := hU
    let n : ℤ := 2 * (r : ℤ)
    refine ⟨M⟦-n⟧, ⟨?_⟩, ⟨?_⟩⟩
    · exact DerivedCategory.shiftTensorShiftIso _ _ _ n (-n) ≪≫
        (shiftFunctor _ _).mapIso a ≪≫
        (shiftFunctorZero' _ (n + -n) (by omega)).app _
    · exact DerivedCategory.shiftTensorShiftIso _ _ _ (-n) n ≪≫
        (shiftFunctor _ _).mapIso b ≪≫
        (shiftFunctorZero' _ (-n + n) (by omega)).app _
  have := hL.isIso_ev (𝟙_ _)
  unfold sourceEvaluation
  infer_instance

/-- The degree-zero regular coefficient complex, using the published single functor.
Source: lem-fd-character-integral, constant coefficient source
(blueprint: def-wft-affine-character-trace). -/
def constantComplex (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u}) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S)) :=
  (DerivedCategory.singleFunctor _ 0).obj (Mod.regular (condensedRingObj Λ S))

/-- Pullback of the constant complex, through the specified single/unit comparisons
and the published derived pullback unit. Source: lem-fd-character-integral, constant
coefficient base change (blueprint: def-wft-affine-character-trace). -/
def constantPullbackIso (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar Λ f).leftDerivedFunctor.obj (constantComplex Λ Y) ≅
      constantComplex Λ X :=
  (CondensedRing.upperStar Λ f).leftDerivedFunctor.mapIso
      (DerivedCategory.singleFunctorObjUnitIso _) ≪≫
    CondensedRing.leftDerivedUpperStarUnitIso Λ f ≪≫
    (DerivedCategory.singleFunctorObjUnitIso _).symm

/-- The negative shifted coefficient line, displayed in the ordinary condensed-E
module category. This fixes the coefficient presentation before composing functors.
Source: lem-fd-character-integral, target E(-r)[-2r]
(blueprint: def-wft-affine-character-trace). -/
def referenceTarget (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (K : Type u) [Field K] (r : ℕ) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) (Spec (.of K)))) :=
  negativeTate ell (.rational E) (Spec (.of K)) r

/-- The algebraic-closure embedding gives the reference base change.
Source: lem-fd-character-integral, arbitrary Omega paragraph
(blueprint: def-wft-affine-character-trace). -/
@[irreducible]
def baseMap (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] :
    Spec (.of Ω) ⟶ Spec (.of (AlgebraicClosure k)) :=
  Spec.map (CommRingCat.ofHom (IsAlgClosed.lift : AlgebraicClosure k →ₐ[k] Ω).toRingHom)

/-- The coordinatewise affine-space square is Cartesian for arbitrary base change.
Source: lem-fd-character-integral, final paragraph
(blueprint: def-wft-affine-character-trace).
Proof: affine space represents tuples of global sections; base change preserves
that representing functor. Induct through the ordered affine-line tower, starting
with the identity square at r=0. No finite-type condition on the base map occurs. -/
theorem affineSquare {S' S : Scheme.{u}} (g : S' ⟶ S) (r : ℕ) :
    IsPullback (affineTraceMap g r) (affineTraceProjection S' r)
      (affineTraceProjection S r) g := by
  induction r with
  | zero => exact IsPullback.id_vert g
  | succ r ih =>
    exact (AffineSpace.isPullback_map (n := PUnit.{u + 1})
      (affineTraceMap g r)).paste_vert ih

/-- The reference compactification pulled back along the actual coordinate square.
Source: det-prop-sf-cbc (b) (blueprint: def-wft-affine-character-trace). -/
@[irreducible]
def baseCompactification {S' S : Scheme.{u}} [IsNoetherian S] (g : S' ⟶ S) (r : ℕ) :
    Compactification (affineTraceProjection S' r) :=
  (HasCompactification.compactification (affineTraceProjection S r)).ofIsPullback
    (affineSquare g r)

/-- The named compact-support proper/open exchange of det-prop-sf-cbc, in the
actual affine-space Cartesian square. Source: det-prop-sf-cbc (b), beta then
proper mate (blueprint: def-wft-affine-character-trace). -/
@[irreducible]
def exchange (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S' S : Scheme.{u}} [IsNoetherian S] (g : S' ⟶ S) (r : ℕ) :
    compactPush Λ
        (HasCompactification.compactification (affineTraceProjection S r)) ⋙
      (CondensedRing.upperStar Λ g).leftDerivedFunctor ⟶
    (CondensedRing.upperStar Λ (affineTraceMap g r)).leftDerivedFunctor ⋙
      compactPush Λ
        (baseCompactification g r) := by
  unfold baseCompactification
  let c := HasCompactification.compactification (affineTraceProjection S r)
  exact ((compactSupportCondensedFormalism Λ).shriekBaseChange c
    (c.ofIsPullback (affineSquare g r)) (pullback.fst c.g g)
    (c.isPullback_i_ofIsPullback (affineSquare g r))
    (c.isPullback_g_ofIsPullback (affineSquare g r)).flip).natTrans

/-- The component of the specified compact-support exchange on constant coefficients.
Source: det-prop-sf-cbc (b), the coefficient-complex component
(blueprint: def-wft-affine-character-trace). -/
@[irreducible]
def constantExchange (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S' S : Scheme.{u}} [IsNoetherian S]
    (g : S' ⟶ S) (r : ℕ) :=
  (exchange Λ g r).app (constantComplex Λ (affineTraceTower S r))

/-- Invertibility of that specified exchange on the constant coefficient complex.
Source: det-prop-sf-cbc (b), specialized to affine space over an algebraically
closed field (blueprint: def-wft-affine-character-trace).
Proof: the affine projection and its compactification are finite type over a field
and Noetherian. The coefficient module is constructible. Apply clause (b) to the
literal pullback square, then transport through affineSquare.isoPullback. The
normalized open/proper comparisons identify the transported map with exchange.
The theorem permits arbitrary S', so no finite-type extension hypothesis is used. -/
theorem exchange_isIso (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (K : Type u) [Field K] [IsAlgClosed K] (hEll : IsUnit (ell : K))
    {S' : Scheme.{u}} (g : S' ⟶ Spec (.of K)) (r : ℕ) :
    IsIso (constantExchange (Profinite.continuousMapRingObj E) g r) := by
  sorry

/-- Actual compact sections on the ordered affine-space model, using the reference
compactification pulled back to Omega. This fixes the compactification presentation
in both clauses of the integral statement. Source: lem-fd-character-integral,
final paragraph (blueprint: def-wft-affine-character-trace). -/
abbrev compactSections (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k Ω : Type u) [Field k] [Field Ω]
    [Algebra k Ω] [IsAlgClosed Ω] (r : ℕ) :=
  condensedRingCompactCoefficientComplex Λ (baseCompactification (baseMap k Ω) r)

/-- The negative Tate coefficient object over Omega, canonically presented as
pullback of the reference line. Source: lem-fd-character-integral, final paragraph
(blueprint: def-wft-affine-character-trace). -/
@[irreducible]
def target (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] (r : ℕ) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) (Spec (.of Ω)))) :=
  (CondensedRing.upperStar (Profinite.continuousMapRingObj E) (baseMap k Ω)).leftDerivedFunctor.obj
    (referenceTarget ell E (AlgebraicClosure k) r)

/-- Compact support of the canonical pullback comparison for the constant complex.
Source: lem-fd-character-integral, constant-source base change
(blueprint: def-wft-affine-character-trace). -/
@[irreducible]
def constantSourceMap (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S' S : Scheme.{u}} [IsNoetherian S]
    (g : S' ⟶ S) (r : ℕ) :=
  (compactPush Λ
    (baseCompactification g r)).map (constantPullbackIso Λ (affineTraceMap g r)).inv

/-- The inverse of precisely the compact-support exchange at the constant complex.
Source: det-prop-sf-cbc (b), arbitrary-base exchange
(blueprint: def-wft-affine-character-trace). -/
@[irreducible]
def constantExchangeInverse (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (K : Type u) [Field K] [IsAlgClosed K] (hEll : IsUnit (ell : K))
    {S' : Scheme.{u}} (g : S' ⟶ Spec (.of K)) (r : ℕ) :=
  letI := exchange_isIso ell E K hEll g r
  (asIso (constantExchange (Profinite.continuousMapRingObj E) g r)).inv

end AlgebraicGeometry.ProEtale.AffineCharacterTrace
