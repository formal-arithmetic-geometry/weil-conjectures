/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Sheaf.Paper.FiniteTorAmplitudeProEtaleModule
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.FiniteOpenClosedRecollement

import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.OpenImmersionHigherDirectImages
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.AlgebraicGeometry.PullbackBoundedConstructible
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.SfIntegralDirectImageConstructible
import Sheaf.Paper.SfIntegralConstructible
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Paper.CompletedPullbackReduction
import Sheaf.Paper.PerfectProjectionFormula
import Sheaf.Paper.ProjectionMateExact
import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Finite.Exact
import Sheaf.AlgebraicGeometry.DerivedOpenImmersionFullyFaithful
import Sheaf.AlgebraicGeometry.OrdinaryDerivedOpenClosedAdjunctions
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.Pullback
import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.Paper.PbcRationalTransport
import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.PbcScalarExtension
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.PbcDescentFunctors
import Sheaf.Paper.PbcVerdierAxioms
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.ProEtaleResidueTorTest
import Sheaf.AlgebraicGeometry.ResidueTorAmplitudeTest
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import Sheaf.AlgebraicGeometry.EtaleDirectImageVanishing
import Sheaf.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension
import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.RingTheory.Etale.LocalDimension
import Sheaf.AlgebraicGeometry.QcqsHigherDirectImage
import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import Sheaf.Paper.FiniteFieldFiber
import Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula
import Sheaf.Paper.FiniteCtfTriangulated
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.Paper.IntegralCtfTriangulated
import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition

/-! # Supported localization at every coefficient stage

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-localization,
proposition prop-sf-localization-all-stages
(blueprint: prop-sf-localization-all-stages).

The records below only package the clauses of the proposition. They do not assume
existence of any of its adjoints or connecting arrows.

## Main statements

- `sfLocalizationAllStages`: the four coefficient stages and their finite-Tor bounds.
- `sfLocalizationExceptionalLimit`: the integral exceptional inverse-limit formula.
- `sfLocalizationAllStages_weil`: equivariance for a pair descending to the finite field.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u v c h a b

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The supported triangle with its prescribed adjunction maps, in an ambient
triangulated category. The category C can be a full constructible subcategory;
its inclusion V records where distinguishedness and shifts are tested.
Source: blueprint supported localization, clauses (2)--(4)
(blueprint: prop-sf-localization-all-stages). -/
structure SfSupportedLocalization
    {C Z U : Type c} [Category.{h} C] [Category.{h} Z] [Category.{h} U]
    {A : Type a} [Category.{b} A] [Preadditive A] [HasZeroObject A]
    [HasShift A ℤ] [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    {B D : Type a} [Category.{b} B] [Category.{b} D]
    [HasZeroMorphisms B]
    (V : C ⥤ A) (W : Z ⥤ B) (_T : U ⥤ D) where
  iPull : C ⥤ Z
  jPull : C ⥤ U
  iPush : Z ⥤ C
  jPush : U ⥤ C
  exceptional : C ⥤ Z
  closedAdjunction : iPull ⊣ iPush
  openAdjunction : jPull ⊣ jPush
  exceptionalAdjunction : iPush ⊣ exceptional
  boundary : jPull ⋙ jPush ⋙ V ⟶ exceptional ⋙ iPush ⋙ V ⋙ shiftFunctor A (1 : ℤ)
  distinguished (K : C) :
    Triangle.mk (V.map (exceptionalAdjunction.counit.app K))
      (V.map (openAdjunction.unit.app K)) (boundary.app K) ∈ distTriang A
  unique_boundary (K : C)
      (δ : V.obj (jPush.obj (jPull.obj K)) ⟶
        (V.obj (iPush.obj (exceptional.obj K)))⟦(1 : ℤ)⟧) :
    Triangle.mk (V.map (exceptionalAdjunction.counit.app K))
      (V.map (openAdjunction.unit.app K)) δ ∈ distTriang A → δ = boundary.app K
  orthogonal (K : C) (m : ℤ) :
    Subsingleton ((V.obj (iPush.obj (exceptional.obj K)))⟦m⟧ ⟶
      V.obj (jPush.obj (jPull.obj K)))
  exceptional_open_zero (G : U) : IsZero (W.obj (exceptional.obj (jPush.obj G)))
  exceptional_unit (Q : Z) : IsIso (exceptionalAdjunction.unit.app Q)

/-- The finite-Tor clauses, including the specified quantitative bounds. The
interval predicates use the actual all-module Tor tests of the coefficient stage.
Source: blueprint supported localization, clauses (1')--(4')
(blueprint: prop-sf-localization-all-stages). -/
structure SfSupportedLocalizationTor
    {C Z U : Type c} [Category.{h} C] [Category.{h} Z] [Category.{h} U]
    {A : Type a} [Category.{b} A] [Preadditive A] [HasZeroObject A]
    [HasShift A ℤ] [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    {B D : Type a} [Category.{b} B] [Category.{b} D] [HasZeroMorphisms B]
    {V : C ⥤ A} {W : Z ⥤ B} {T : U ⥤ D}
    (S : SfSupportedLocalization V W T)
    (PX : C → Prop) (PZ : Z → Prop) (PU : U → Prop)
    (IX : C → ℤ → ℤ → Prop) (IZ : Z → ℤ → ℤ → Prop)
    (IU : U → ℤ → ℤ → Prop) (N : ℤ) : Prop where
  open_preserves (G : U) : PU G → PX (S.jPush.obj G)
  exceptional_preserves (K : C) : PX K → PZ (S.exceptional.obj K)
  closed_preserves (Q : Z) : PZ Q → PX (S.iPush.obj Q)
  closed_pull_preserves (K : C) : PX K → PZ (S.iPull.obj K)
  open_pull_preserves (K : C) : PX K → PU (S.jPull.obj K)
  open_interval (G : U) (r s : ℤ) : IU G r s → IX (S.jPush.obj G) r (s + N)
  exceptional_interval (K : C) (r s : ℤ) : IX K r s →
    IZ (S.exceptional.obj K) r (s + N + 1)
  closed_interval (Q : Z) (r s : ℤ) : IZ Q r s → IX (S.iPush.obj Q) r s
  closed_pull_interval (K : C) (r s : ℤ) : IX K r s → IZ (S.iPull.obj K) r s
  open_pull_interval (K : C) (r s : ℤ) : IX K r s → IU (S.jPull.obj K) r s

/-- The intrinsic finite constructible category, using the recorded predicate.
Source: blueprint supported localization, finite stage
(blueprint: prop-sf-localization-all-stages). -/
abbrev SfLocalizationFiniteCategory (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (X : Scheme.{u}) :=
  (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).FullSubcategory

/-- Compatibility of a restricted adjunction unit with the specified ambient unit.
This is the commuting equation for its two comparison isomorphisms.
Source: blueprint supported localization, canonical maps in (1)--(2)
(blueprint: prop-sf-localization-all-stages). -/
def SfLocalizationUnitCompatibility
    {C₀ D₀ : Type c} [Category.{h} C₀] [Category.{h} D₀]
    {C D : Type a} [Category.{b} C] [Category.{b} D]
    (V : C₀ ⥤ C) (W : D₀ ⥤ D) {L : C₀ ⥤ D₀} {R : D₀ ⥤ C₀}
    {F : C ⥤ D} {G : D ⥤ C} (restricted : L ⊣ R) (ambient : F ⊣ G)
    (leftComparison : L ⋙ W ≅ V ⋙ F) (rightComparison : R ⋙ V ≅ W ⋙ G) : Prop :=
  ∀ K : C₀, V.map (restricted.unit.app K) ≫
    rightComparison.hom.app (L.obj K) ≫ G.map (leftComparison.hom.app K) =
      ambient.unit.app (V.obj K)

/-- The unit equation for two adjunctions under specified functor comparisons.
This is the literal commuting equation, with no invertibility or coherence added.
Source: blueprint supported localization, coefficient-passage unit normalization
(blueprint: prop-sf-localization-all-stages). -/
def SfLocalizationScalarUnitCompatibility
    {C₀ D₀ : Type c} [Category.{h} C₀] [Category.{h} D₀]
    {C₁ D₁ : Type a} [Category.{b} C₁] [Category.{b} D₁]
    (FX : C₀ ⥤ C₁) (FZ : D₀ ⥤ D₁)
    {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀} {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
    (adj₀ : L₀ ⊣ R₀) (adj₁ : L₁ ⊣ R₁)
    (left : FX ⋙ L₁ ≅ L₀ ⋙ FZ) (right : FZ ⋙ R₁ ≅ R₀ ⋙ FX) : Prop :=
  ∀ K : C₀, adj₁.unit.app (FX.obj K) ≫ R₁.map (left.hom.app K) ≫
    right.hom.app (L₀.obj K) = FX.map (adj₀.unit.app K)

/-- The counit equation for the same specified scalar comparisons of adjunctions.
This names its exact equation so elaboration shares the categorical calculation.
Source: blueprint supported localization, coefficient-passage counit normalization
(blueprint: prop-sf-localization-all-stages). -/
def SfLocalizationScalarCounitCompatibility
    {C₀ D₀ : Type c} [Category.{h} C₀] [Category.{h} D₀]
    {C₁ D₁ : Type a} [Category.{b} C₁] [Category.{b} D₁]
    (FX : C₀ ⥤ C₁) (FZ : D₀ ⥤ D₁)
    {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀} {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
    (adj₀ : L₀ ⊣ R₀) (adj₁ : L₁ ⊣ R₁)
    (left : FX ⋙ L₁ ≅ L₀ ⋙ FZ) (right : FZ ⋙ R₁ ≅ R₀ ⋙ FX) : Prop :=
  ∀ Q : D₀, L₁.map (right.hom.app Q) ≫ left.hom.app (R₀.obj Q) ≫
    FZ.map (adj₀.counit.app Q) = adj₁.counit.app (FZ.obj Q)

/-- Actual finite-stage operations and their constructible adjunctions. The
normalizations identify every functor with the recorded intrinsic operation.
Source: blueprint supported localization, clauses (1)--(4), finite stage
(blueprint: prop-sf-localization-all-stages). -/
structure SfFiniteLocalization
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (k : Type u) [Field k]
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] where
  supported : SfSupportedLocalization
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z).ι
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) U).ι
  closed_pull : supported.iPull ⋙
      (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z).ι ≅
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι ⋙
      finiteDerivedPullback l E n i
  open_pull : supported.jPull ⋙
      (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) U).ι ≅
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι ⋙
      finiteDerivedPullback l E n j
  closed_push : supported.iPush ⋙
      (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι ≅
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z).ι ⋙
      proEtaleConstantDerivedDirectImage i (Padic.coefficientExtensionRing l E (n + 1))
  open_push : supported.jPush ⋙
      (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι ≅
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) U).ι ⋙
      proEtaleConstantDerivedDirectImage j (Padic.coefficientExtensionRing l E (n + 1))
  open_unit : SfLocalizationUnitCompatibility
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) U).ι
    supported.openAdjunction
    (finiteRecollementDerivedAdjunction j
      (Padic.coefficientExtensionRing l E (n + 1))) open_pull open_push
  closed_unit : SfLocalizationUnitCompatibility
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z).ι
    supported.closedAdjunction
    (finiteRecollementDerivedAdjunction i
      (Padic.coefficientExtensionRing l E (n + 1))) closed_pull closed_push
  exceptional_comparison : supported.exceptional ⋙
      (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z).ι ≅
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι ⋙
      ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1))
        (Compactification.ofIsProper i)
  tor (d c : ℕ) :
    ((IsEmpty U ∧ d = 0) ∨ (Nonempty U ∧
      topologicalKrullDim U = (d : WithBot ℕ∞))) →
    HasTorsionEtaleCohomologicalDimensionLE (Spec (.of k)) c →
    SfSupportedLocalizationTor supported
      (fun K ↦ finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X K.obj)
      (fun K ↦ finiteTorConstructible l E (n + 1) (Nat.succ_pos n) Z K.obj)
      (fun K ↦ finiteTorConstructible l E (n + 1) (Nat.succ_pos n) U K.obj)
      (fun K ↦ HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1)) K.obj)
      (fun K ↦ HasProEtaleTorAmplitude Z (Padic.coefficientExtensionRing l E (n + 1)) K.obj)
      (fun K ↦ HasProEtaleTorAmplitude U (Padic.coefficientExtensionRing l E (n + 1)) K.obj)
      (2 * (d : ℤ) + (c : ℤ))

/-- The canonical field map into a residue field, through global sections.
Source: blueprint supported localization, field-base hypothesis
(blueprint: prop-sf-localization-all-stages). -/
def sfLocalizationResidueMap (k : Type u) [Field k]
    (X : Scheme.{u}) (t : X ⟶ Spec (.of k)) (x : X) :
    CommRingCat.of k ⟶ X.residueField x :=
  (Scheme.ΓSpecIso (.of k)).inv ≫ t.appTop ≫ X.Γevaluation x

/-- The inherited invertibility instance used in the recorded pullbacks.
This is the image of the given unit under the canonical residue-field map.
Source: blueprint supported localization, coefficient hypothesis
(blueprint: prop-sf-localization-all-stages). -/
@[instance_reducible]
def sfLocalizationPrimeInvertible (k : Type u) [Field k] (l : ℕ)
    (hl : IsUnit (l : k)) (X : Scheme.{u}) (t : X ⟶ Spec (.of k)) (x : X) :
    Invertible (l : X.residueField x) :=
  (Eq.mp (congrArg IsUnit (map_natCast (sfLocalizationResidueMap k X t x).hom l))
    (hl.map (sfLocalizationResidueMap k X t x).hom)).invertible

/-- An integral Tor interval means the same interval at every positive reduction.
Source: blueprint supported localization, clauses (1')--(3'), integral stage
(blueprint: prop-sf-localization-all-stages). -/
def SfLocalizationIntegralInterval (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (K : sfIntegralConstructibleCategory l E X) (r s : ℤ) : Prop :=
  r ≤ s ∧ ∀ n : ℕ, HasProEtaleTorAmplitude X
    (Padic.coefficientExtensionRing l E (n + 1))
    ((scalarReductionDerivedExtension.{u, u} l E X n).obj K.obj) r s

/-- Derived reduction restricted to the exact recorded constructible categories.
Its proof is the constructibility clause of the integral object's membership proof.
Source: blueprint supported localization, integral reduction paragraph
(blueprint: prop-sf-localization-all-stages). -/
def sfLocalizationConstructibleReduction (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (n : ℕ) :
    sfIntegralConstructibleCategory l E X ⥤ SfLocalizationFiniteCategory l E n X :=
  (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).lift
    ((sfIntegralConstructible l E X).ι ⋙ scalarReductionDerivedExtension.{u, u} l E X n)
    (fun K ↦ (K.property.2.choose_spec.choose_spec.2 n).1)

/-- Integral supported localization, with its ordinary completed direct images,
actual completed pullbacks, and exceptional reductions. The natural reduction
isomorphisms, together with completeness of their source, express the inverse-limit
formula: the tower transitions are the transported canonical quotient transitions.
Source: blueprint supported localization, integral clauses (1)--(4), (1')--(4')
(blueprint: prop-sf-localization-all-stages). -/
structure SfIntegralLocalization
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    {X Z U : Scheme.{u}} (t : X ⟶ Spec (.of k))
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] where
  supported : SfSupportedLocalization
    (sfIntegralConstructible l E X).ι (sfIntegralConstructible l E Z).ι
    (sfIntegralConstructible l E U).ι
  closed_pull : supported.iPull ≅
    @constructibleIntegralPullback l _ E _ _ _ Z X i
      (sfLocalizationPrimeInvertible k l hl Z (i ≫ t))
      (sfLocalizationPrimeInvertible k l hl X t)
  open_pull : supported.jPull ≅
    @constructibleIntegralPullback l _ E _ _ _ U X j
      (sfLocalizationPrimeInvertible k l hl U (j ≫ t))
      (sfLocalizationPrimeInvertible k l hl X t)
  closed_push : supported.iPush ⋙ (sfIntegralConstructible l E X).ι ≅
    (sfIntegralConstructible l E Z).ι ⋙ sfCompletedDerivedDirectImage l E i
  open_push : supported.jPush ⋙ (sfIntegralConstructible l E X).ι ≅
    (sfIntegralConstructible l E U).ι ⋙ sfCompletedDerivedDirectImage l E j
  closed_limit (Q : sfIntegralConstructibleCategory l E Z) :
    ∃ hp : HasProduct (sfDirectImageTerm l E i Q.obj),
      ∃ L : @SfIntegralDirectImage l _ E _ _ _ Z X i Q.obj hp,
        Nonempty (L.obj ≅ (supported.iPush.obj Q).obj) ∧
          ∀ n : ℕ, IsIso (@sfDirectImageReductionComparison l _ E _ _ _ Z X i Q.obj hp L n)
  open_limit (G : sfIntegralConstructibleCategory l E U) :
    ∃ hp : HasProduct (sfDirectImageTerm l E j G.obj),
      ∃ L : @SfIntegralDirectImage l _ E _ _ _ U X j G.obj hp,
        Nonempty (L.obj ≅ (supported.jPush.obj G).obj) ∧
          ∀ n : ℕ, IsIso (@sfDirectImageReductionComparison l _ E _ _ _ U X j G.obj hp L n)
  finiteStages (n : ℕ) : SfFiniteLocalization l E n k i j
  closed_reduction (n : ℕ) :
    supported.iPush ⋙ sfLocalizationConstructibleReduction l E X n ≅
      sfLocalizationConstructibleReduction l E Z n ⋙ (finiteStages n).supported.iPush
  open_reduction (n : ℕ) :
    supported.jPush ⋙ sfLocalizationConstructibleReduction l E X n ≅
      sfLocalizationConstructibleReduction l E U n ⋙ (finiteStages n).supported.jPush
  open_pull_reduction (n : ℕ) :
    supported.jPull ⋙ sfLocalizationConstructibleReduction l E U n ≅
      sfLocalizationConstructibleReduction l E X n ⋙ (finiteStages n).supported.jPull
  exceptional_reduction (n : ℕ) :
    supported.exceptional ⋙ sfLocalizationConstructibleReduction l E Z n ≅
      sfLocalizationConstructibleReduction l E X n ⋙ (finiteStages n).supported.exceptional
  exceptional_counit_reduction (n : ℕ) (K : sfIntegralConstructibleCategory l E X) :
    (sfLocalizationConstructibleReduction l E X n).map
        (supported.exceptionalAdjunction.counit.app K) =
      (closed_reduction n).hom.app (supported.exceptional.obj K) ≫
        (finiteStages n).supported.iPush.map ((exceptional_reduction n).hom.app K) ≫
        (finiteStages n).supported.exceptionalAdjunction.counit.app
          ((sfLocalizationConstructibleReduction l E X n).obj K)
  open_unit_reduction (n : ℕ) (K : sfIntegralConstructibleCategory l E X) :
    (sfLocalizationConstructibleReduction l E X n).map
        (supported.openAdjunction.unit.app K) ≫
      (open_reduction n).hom.app (supported.jPull.obj K) ≫
        (finiteStages n).supported.jPush.map ((open_pull_reduction n).hom.app K) =
      (finiteStages n).supported.openAdjunction.unit.app
        ((sfLocalizationConstructibleReduction l E X n).obj K)
  tor (d c : ℕ) :
    ((IsEmpty U ∧ d = 0) ∨ (Nonempty U ∧
      topologicalKrullDim U = (d : WithBot ℕ∞))) →
    HasTorsionEtaleCohomologicalDimensionLE (Spec (.of k)) c →
    SfSupportedLocalizationTor supported
      (fun K ↦ finiteTorConstructibleIntegral l E X K.obj)
      (fun K ↦ finiteTorConstructibleIntegral l E Z K.obj)
      (fun K ↦ finiteTorConstructibleIntegral l E U K.obj)
      (SfLocalizationIntegralInterval l E X)
      (SfLocalizationIntegralInterval l E Z)
      (SfLocalizationIntegralInterval l E U) (2 * (d : ℤ) + (c : ℤ))

section IntegralLimit

variable {l : ℕ} [Fact l.Prime]
  {E : Type u} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {k : Type u} [Field k] {hl : IsUnit (l : k)}
  {X Z U : Scheme.{u}} {t : X ⟶ Spec (.of k)}
  {i : Z ⟶ X} {j : U ⟶ X} [IsClosedImmersion i] [IsOpenImmersion j]
  (S : SfIntegralLocalization l E k hl t i j)
  (K : sfIntegralConstructibleCategory l E X)

/-- The n-th term of the integral exceptional-image formula, with its finite
coefficient action retained until restriction. Source: blueprint localization (2)
(blueprint: prop-sf-localization-all-stages). -/
abbrev sfLocalizationExceptionalTerm (n : ℕ) :=
  (scalarReductionDerivedRestriction.{u, u} l E Z n).obj
    ((S.finiteStages n).supported.exceptional.obj
      ((sfLocalizationConstructibleReduction l E X n).obj K)).obj

/-- The reduction comparison fixed by the exceptional counit normalization.
Source: blueprint localization (2), integral reduction comparison
(blueprint: prop-sf-localization-all-stages). -/
def sfLocalizationExceptionalComparison (n : ℕ) :=
  (scalarReductionDerivedRestriction.{u, u} l E Z n).mapIso
    ((intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z).ι.mapIso
      ((S.exceptional_reduction n).app K))

/-- The quotient transition of the exceptional-image tower, transported through
the counit-normalized finite reductions. Thus it retains the quotient coherence
of the actual derived reduction tower. Source: blueprint localization (2)
(blueprint: prop-sf-localization-all-stages). -/
def sfLocalizationExceptionalTransition (n : ℕ) :
    sfLocalizationExceptionalTerm S K (n + 1) ⟶ sfLocalizationExceptionalTerm S K n :=
  (sfLocalizationExceptionalComparison S K (n + 1)).inv ≫
    (sfDerivedReductionTransition l E Z n).app (S.supported.exceptional.obj K).obj ≫
    (sfLocalizationExceptionalComparison S K n).hom

set_option linter.unusedVariables false in
/-- The displayed Rlim formula with its actual reduction projections, not just
an isomorphism to an unspecified limit object. Source: blueprint localization (2)
(blueprint: prop-sf-localization-all-stages).
Proof: the exceptional value is an object of sfIntegralConstructibleCategory,
so its defining completeness is the Roos triangle of its canonical reductions.
Whisker each counit-normalized exceptional reduction by exact scalar restriction.
The resulting isomorphisms identify that reduction tower with the displayed
finite-exceptional tower. The definition of the transition conjugates the actual
quotient transitions, so every square commutes. Transport the product and the
Roos triangle through these isomorphisms. Its n-th first-map component is exactly
the canonical reduction unit followed by the specified comparison. This proves
existence of the product, the displayed projection, and distinguishedness. -/
theorem sfLocalizationExceptionalLimit :
    ∃ hp : HasProduct (sfLocalizationExceptionalTerm S K),
      (fun [hprod : HasProduct (sfLocalizationExceptionalTerm S K)] ↦
        ∃ δ : (∏ᶜ (sfLocalizationExceptionalTerm S K)) ⟶
            (S.supported.exceptional.obj K).obj⟦(1 : ℤ)⟧,
          IsDerivedLimitTriangle (sfLocalizationExceptionalTransition S K)
            (S.supported.exceptional.obj K).obj
            (Pi.lift (fun n ↦ (sfDerivedReductionUnit l E Z n).app
              (S.supported.exceptional.obj K).obj ≫
                (sfLocalizationExceptionalComparison S K n).hom)) δ) (hprod := hp) := by
  -- Completeness supplies the canonical Roos triangle, including its reduction projections.
  obtain ⟨hp, δ, hδ⟩ := (S.supported.exceptional.obj K).property.1
  let := hp
  let e := sfLocalizationExceptionalComparison S K
  have hp' : HasProduct (sfLocalizationExceptionalTerm S K) :=
    hasProduct_of_equiv_of_iso
      (fun n ↦ (sfDerivedReductionRestricted l E Z n).obj
        (S.supported.exceptional.obj K).obj)
      (sfLocalizationExceptionalTerm S K) (Equiv.refl ℕ) (fun n ↦ (e n).symm)
  refine ⟨hp', ?_⟩
  let := hp'
  let a : (∏ᶜ fun n ↦ (sfDerivedReductionRestricted l E Z n).obj
      (S.supported.exceptional.obj K).obj) ≅ ∏ᶜ (sfLocalizationExceptionalTerm S K) :=
    { hom := Limits.Pi.map (fun n ↦ (e n).hom)
      inv := Limits.Pi.map (fun n ↦ (e n).inv)
      hom_inv_id := by
        rw [Limits.Pi.map_comp_map]
        simp only [Iso.hom_inv_id, Limits.Pi.map_id]
      inv_hom_id := by
        rw [Limits.Pi.map_comp_map]
        simp only [Iso.inv_hom_id, Limits.Pi.map_id] }
  -- The prescribed quotient transitions are conjugate through the reduction comparisons.
  have ha : a.hom ≫ towerTransitionEndomorphism (sfLocalizationExceptionalTransition S K) =
      towerTransitionEndomorphism
        (fun n ↦ (sfDerivedReductionTransition l E Z n).app
          (S.supported.exceptional.obj K).obj) ≫ a.hom := by
    dsimp only [a]
    apply towerTransitionEndomorphism_natural_backward
      (fun n ↦ (sfDerivedReductionTransition l E Z n).app
        (S.supported.exceptional.obj K).obj)
      (sfLocalizationExceptionalTransition S K) (fun n ↦ (e n).hom)
    intro n
    change (e (n + 1)).hom ≫
        ((e (n + 1)).inv ≫ _ ≫ (e n).hom) = _
    simp only [Iso.hom_inv_id_assoc]
  -- Transport all three arrows; in particular, retain the specified first-map components.
  refine ⟨a.inv ≫ δ, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hδ
  refine Triangle.isoMk _ _ (Iso.refl _) a.symm a.symm ?_ ?_ ?_
  · change (Pi.lift (fun n ↦ (sfDerivedReductionUnit l E Z n).app
        (S.supported.exceptional.obj K).obj ≫ (e n).hom)) ≫ a.inv =
      𝟙 _ ≫ Pi.lift (fun n ↦ (sfDerivedReductionUnit l E Z n).app
        (S.supported.exceptional.obj K).obj)
    apply Pi.hom_ext
    intro n
    simp [a, Category.assoc]
  · change towerTransitionEndomorphism (sfLocalizationExceptionalTransition S K) ≫
        a.inv = a.inv ≫ towerTransitionEndomorphism _
    apply (cancel_mono a.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← ha, Iso.inv_hom_id_assoc]
  · change (a.inv ≫ δ) ≫ (shiftFunctor _ (1 : ℤ)).map (𝟙 _) = a.inv ≫ δ
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

end IntegralLimit

/-- Rational supported localization in the raw scalar localization. Its three
right adjoints are identified with rationalizations of the integral operations.
In particular the exceptional operation is the specified one, rather than an
unspecified extra right adjoint. At field coefficients every object is finite Tor.
Source: blueprint supported localization, rational clauses (1)--(4)
(blueprint: prop-sf-localization-all-stages). -/
structure SfRationalLocalization
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    {X Z U : Scheme.{u}} (t : X ⟶ Spec (.of k))
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] where
  integral : SfIntegralLocalization l E k hl t i j
  supported : SfSupportedLocalization
    (𝟭 (sfRationalConstructibleCategory l E X))
    (𝟭 (sfRationalConstructibleCategory l E Z))
    (𝟭 (sfRationalConstructibleCategory l E U))
  closed_pull : supported.iPull =
    @rationalDerivedPullback l _ E _ _ _ Z X i
      (sfLocalizationPrimeInvertible k l hl Z (i ≫ t))
      (sfLocalizationPrimeInvertible k l hl X t)
  open_pull : supported.jPull =
    @rationalDerivedPullback l _ E _ _ _ U X j
      (sfLocalizationPrimeInvertible k l hl U (j ≫ t))
      (sfLocalizationPrimeInvertible k l hl X t)
  closed_push : sfRationalConstructibleLocalization l E Z ⋙ supported.iPush ≅
    integral.supported.iPush ⋙ sfRationalConstructibleLocalization l E X
  open_push : sfRationalConstructibleLocalization l E U ⋙ supported.jPush ≅
    integral.supported.jPush ⋙ sfRationalConstructibleLocalization l E X
  exceptional : sfRationalConstructibleLocalization l E X ⋙ supported.exceptional ≅
    integral.supported.exceptional ⋙ sfRationalConstructibleLocalization l E Z
  open_pull_localization : sfRationalConstructibleLocalization l E X ⋙ supported.jPull ≅
    integral.supported.jPull ⋙ sfRationalConstructibleLocalization l E U
  counit_localization : SfLocalizationScalarCounitCompatibility
    (sfRationalConstructibleLocalization l E Z) (sfRationalConstructibleLocalization l E X)
    integral.supported.exceptionalAdjunction supported.exceptionalAdjunction
    closed_push exceptional
  open_unit_localization : SfLocalizationScalarUnitCompatibility
    (sfRationalConstructibleLocalization l E X) (sfRationalConstructibleLocalization l E U)
    integral.supported.openAdjunction supported.openAdjunction open_pull_localization open_push
  unit_localization : SfLocalizationScalarUnitCompatibility
    (sfRationalConstructibleLocalization l E Z) (sfRationalConstructibleLocalization l E X)
    integral.supported.exceptionalAdjunction supported.exceptionalAdjunction
    closed_push exceptional


/-- The finite-stage comparison equations for supported localization, stated once
in categorical variables so their elaboration does not repeatedly unfold the
p-adic field structures. These are the closed/open image and exceptional comparisons,
with their actual counit, open unit and exceptional unit normalizations.
Source: blueprint supported localization, algebraically closed coefficient passage
(blueprint: prop-sf-localization-all-stages). -/
structure SfLocalizationStageComparison
    {C₀ Z₀ U₀ : Type c} [Category.{h} C₀] [Category.{h} Z₀] [Category.{h} U₀]
    [Preadditive C₀] [HasZeroObject C₀] [HasShift C₀ ℤ]
    [∀ n : ℤ, (shiftFunctor C₀ n).Additive] [Pretriangulated C₀]
    [HasZeroMorphisms Z₀]
    {C₁ Z₁ U₁ : Type a} [Category.{b} C₁] [Category.{b} Z₁] [Category.{b} U₁]
    [Preadditive C₁] [HasZeroObject C₁] [HasShift C₁ ℤ]
    [∀ n : ℤ, (shiftFunctor C₁ n).Additive] [Pretriangulated C₁]
    [HasZeroMorphisms Z₁]
    (S₀ : SfSupportedLocalization (𝟭 C₀) (𝟭 Z₀) (𝟭 U₀))
    (S₁ : SfSupportedLocalization (𝟭 C₁) (𝟭 Z₁) (𝟭 U₁))
    (FX : C₀ ⥤ C₁) (FZ : Z₀ ⥤ Z₁) (FU : U₀ ⥤ U₁) where
  closed_push : FZ ⋙ S₁.iPush ≅ S₀.iPush ⋙ FX
  open_push : FU ⋙ S₁.jPush ≅ S₀.jPush ⋙ FX
  exceptional : FX ⋙ S₁.exceptional ≅ S₀.exceptional ⋙ FZ
  open_pull : FX ⋙ S₁.jPull ≅ S₀.jPull ⋙ FU
  counit : SfLocalizationScalarCounitCompatibility FZ FX
    S₀.exceptionalAdjunction S₁.exceptionalAdjunction closed_push exceptional
  open_unit : SfLocalizationScalarUnitCompatibility FX FU
    S₀.openAdjunction S₁.openAdjunction open_pull open_push
  unit : SfLocalizationScalarUnitCompatibility FZ FX
    S₀.exceptionalAdjunction S₁.exceptionalAdjunction closed_push exceptional


/-- Supported localization on the actual common-stage category. The finite-stage
comparisons are natural isomorphisms of functors, including their Hom actions.
The adjunction to the recorded common-stage pullback determines direct image;
the next adjunction determines the exceptional functor uniquely up to the
compatible adjoint isomorphism. No arbitrary map or arbitrary equivalence is used.
Source: blueprint supported localization, algebraically closed clauses (1)--(4)
(blueprint: prop-sf-localization-all-stages). -/
structure SfAlgebraicallyClosedLocalization
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    {X Z U : Scheme.{u}} (t : X ⟶ Spec (.of k))
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] where
  stages (L : AlgebraicallyClosedCoefficients.Index l Ω) :
    SfRationalLocalization l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
      k hl t i j
  supported : SfSupportedLocalization
    (𝟭 (generalAlgebraicallyClosedConstructibleCategory l Ω X))
    (𝟭 (generalAlgebraicallyClosedConstructibleCategory l Ω Z))
    (𝟭 (generalAlgebraicallyClosedConstructibleCategory l Ω U))
  closed_pull : supported.iPull =
    @commonStageDerivedPullback l _ Ω _ _ _ Z X i
      (sfLocalizationPrimeInvertible k l hl Z (i ≫ t))
      (sfLocalizationPrimeInvertible k l hl X t)
  open_pull : supported.jPull =
    @commonStageDerivedPullback l _ Ω _ _ _ U X j
      (sfLocalizationPrimeInvertible k l hl U (j ≫ t))
      (sfLocalizationPrimeInvertible k l hl X t)
  comparison (L : AlgebraicallyClosedCoefficients.Index l Ω) :
    SfLocalizationStageComparison (stages L).supported supported
      (GeneralAlgebraicallyClosedCoefficients.inclusion (Y := X) L)
      (GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Z) L)
      (GeneralAlgebraicallyClosedCoefficients.inclusion (Y := U) L)

/-- Supported localization at every coefficient stage, without imposing a finite
cohomological dimension on the base for clauses (1)--(4). The finite-Tor assertions
carry the separate finite-cd hypothesis in their tor fields.
Source: Weil blueprint, proposition prop-sf-localization-all-stages
(blueprint: prop-sf-localization-all-stages).

Proof plan (the node's steps):

1. Finite-level setting and open direct image. Interfaces phrased with a global finite-field datum
but an arbitrary scheme $T$ are used with an auxiliary finite-field datum of characteristic
different from $\ell$; they impose no map from $T$ to that auxiliary field. In the Weil clause
alone the datum is the actual base-field datum of the statement. The adic-coefficient interfaces
are instantiated with $(A,I)=(\mathcal O_E,(\varpi_E))$: the valuation-ring theorem gives a
Noetherian DVR, the quotient theorem gives finite quotients, and
[lem-weil-pbc-standard-quotients-perfect], with $n\ge1$, gives the augmented resolution $[\mathcal
O_E\xrightarrow{\varpi_E^n}\mathcal O_E]\to A_{E,n}[0]$ in degrees $-1,0$. This verifies
perfectness of the ordinary $\mathcal O_E$-module $A_{E,n}$ in the adic datum; it does not
identify constant and completed coefficient sheaf categories. All schemes in the assertion are
Noetherian: finite type over a field implies Noetherianity, so $j$ is quasi-compact (every open of
a Noetherian space is quasi-compact), and is separated. Write $G\cong\nu_U^*G'$ with $G'$ bounded
constructible, using the constructible-origin equivalence. The comparison for qcqs direct images
gives $Rj_*G\cong\nu_X^*Rj_{\mathrm{et},*}G'$. For each of the finitely many nonzero $\mathcal
H^q(G')$, the open-immersion finiteness theorem makes all $R^pj_*\mathcal H^q(G')$ constructible,
with only finitely many nonzero. The truncation spectral sequence and the Serre property then show
that $Rj_{\mathrm{et},*}G'$ is bounded constructible. Pulling back by the exact $\nu_X^*$ proves
(1) at $A_{E,n}$.

2. Ambient adjoints before localization. Work with $B_X=(A_{E,n})_X$ or $B_X=\widehat{\mathcal
O}_{E,X}$. The coefficient inverse-image theorem identifies the pulled-back rings with $B_Z,B_U$,
respecting quotient projections. Since $j$ is quasi-compact by Step 1,
[lem-sf-ringed-closed-kernel-adjoint] applies. It constructs $i^!_0N=i^*\ker(N\to j_*j^*N)$, its
ambient derived right adjoint $Ri^!_0$, and all four adjunctions needed for the unit's Hom
argument. In particular $i^*i_*\cong1$, $j^*Rj_*\cong1$ and $j^*i_*=0$ on all complexes. Exact
immersion pullback and exact closed pushforward are termwise; the exact-functor factorization
gives their triangulated structures. The K-injective total-derived theorem gives the exact
structure of $Ri^!_0$. None of these inputs uses the supported triangle.

3. The prescribed Hom(-,K) comparison. The ordinary ringed short exact sequence, termwise on $M$,
gives the distinguished triangle $j_!j^*M\to M\to i_*i^*M\to(j_!j^*M)[1]$. Apply Hom(-,K) and
shifts. The four adjunctions of Step 2 identify its outer groups as
$$\operatorname{Hom}(i_*i^*M,K)=\operatorname{Hom}(i^*M,Ri^!_0K)=\operatorname{Hom}(M,i_*Ri^!_0K),$$
$$\operatorname{Hom}(j_!j^*M,K)=\operatorname{Hom}(j^*M,j^*K)=\operatorname{Hom}(M,Rj_*j^*K).$$
The maps are induced by the actual exceptional counit $e$ and open unit $u$: substitute the
adjunction bijections and cancel the adjacent unit/counit pairs. Complete $e$ to a distinguished
triangle. Apply [lem-sf-ordinary-triangle-counit-cone], whose four adjunctions, invertible closed
and open counits, vanishing $j^*i_*$, and ordinary triangle have all just been supplied. Its
specified comparison from the counit cone to $Rj_*j^*K$ is invertible and preserves $u$. Transport
the connecting arrow through that comparison. This proves the ambient supported triangle at both
finite and completed coefficients, with the prescribed first two maps. The same lemma gives
closed-to-open orthogonality for every input and shift.

4. Finite constructible restriction and the determination interface. Step 3 is an ambient
argument, so it does not presuppose boundedness of $Ri^!_0K$. For finite coefficients and
constructible $K$, its third term is bounded constructible by Step 1 and pullback preservation.
The finite bounded constructible subcategory is triangulated; hence $A=i_*Ri^!_0K$ is bounded
constructible. The termwise closed counit of Step 2 gives $Ri^!_0K\cong i^*A$, which is bounded
constructible by the pullback theorem. The ambient adjunction restricts to these full
subcategories. This proves finite-level (2) and the existence in (3). Closed pushforward
preservation and full faithfulness are also supplied by the all-stage closed-unit theorem. The
natural-transformation determination theorem can be applied to the counit $i^*i_*\to1$: both
functors are exact, and the degreewise counit commutes with the usual signed shifts. It is an
isomorphism on sheaves. The truncation triangle of a bounded-cohomology complex has a shift of its
highest cohomology sheaf as last vertex; the first vertex has fewer nonzero cohomology sheaves.
Starting with zero, two-out-of-three propagates invertibility to every bounded complex. This
spells out the unit's determination tool with the shift hypothesis it actually requires; the cone
comparison itself has already been proved for every $M$ in Step 3, without assuming that a
transformation is determined by its values on generators.

5. Integral operations. Put $R=\mathcal O_E$. The DVR and finite-quotient theorems and the
ordinary augmented resolution $[R\xrightarrow{\varpi_E^n}R]\to A_{E,n}[0]$ from the
perfect-quotient theorem verify the Noetherian adic datum, for $n\ge1$. Apply
[prop-weil-pbc-direct-image-limits] to $i,j$: its canonical strict-tower comparison identifies
ordinary completed-ring direct image with $R\varprojlim_n\operatorname{Res}_nRf_{*,n}K_n$,
including finite projection maps and their quotient compatibility. Thus it is precisely the
integral direct image in [def-weil-derived-direct-image]. The constant/completion equivalence
identifies the two completeness conventions, without identifying their ambient module categories.
The integral direct-image constructibility theorem and integral pullback theorem give
constructibility and the required uniform bounds. For reduction detection, a complete $C$ whose
reductions vanish has defining Roos triangle $C\to0\to0\to C[1]$, hence $C=0$. Apply this to the
cone of a morphism: the integral subcategory is triangulated and reduction is exact derived
tensor, so isomorphisms are detected by all reductions.

6. Ordinary and completed immersion pullbacks. Apply
[lem-sf-immersion-completed-pullback-comparison] to $i,j$. Its actual coefficient-ring map is the
canonical inverse-image isomorphism, not a general scalar extension. It identifies ordinary
inverse image with the specified completed pullback on derived-complete objects, including its
completion unit, finite projections and quotient transitions. In particular both inverse images
preserve the precise integral constructible category, with the same uniform cohomological
intervals. The ambient adjunctions of Step 2 therefore restrict, using the direct-image
identifications of Step 5, to the integral operations in the statement. Their unit/counit formulas
are the restrictions of the ambient formulas. Consequently $j^*Rj_*\cong1$, $j^*i_*=0$, and the
orthogonality of Step 3 holds in the integral subcategories.

7. Integral restriction and reduction of the exceptional counit. In the ambient supported triangle
of Step 3, $K$ and $Rj_*j^*K$ are integral constructible by Steps 5-6. Triangulated closure gives
$A=i_*Ri^!_0K$ integral constructible; the invertible closed counit identifies $Ri^!_0K=i^*A$, so
Step 6 restricts the ambient adjunction. Let $T_n$ be derived reduction. Under the canonical
pullback and direct-image projection comparisons, the transpose of $T_n\eta_j$ is
$T_n(\varepsilon_jj^*\circ j^*\eta_j)=1$. Thus the reduced open map is the finite open unit. The
reduced triangle and the finite triangle have identical middle and open vertices and maps. Their
first vertices are closed-supported, by the closed direct-image reduction comparison.
Closed-to-open orthogonality and [lem-weil-pbc-triangle-morphism-extension] (1)-(2) give the
unique triangle morphism with identity middle and open components; [lem-sf-triangle-morphism-iso]
makes the closed component invertible. Applying $i_n^*$ gives $(Ri^!K)_n\cong Ri_n^!K_n$,
preserving the exceptional counit. For $m\ge n$, restrict the $n$-triangle to
$A_{E,m}$-coefficients. The direct-image/restriction-of-scalars comparison identifies its open
vertex with $Rj_{m,*}\operatorname{Res}_{m,n}j_n^*K_n$. Orthogonality therefore holds in this
single category. Both candidate transition comparisons have the same natural middle and open
components, so the uniqueness clause of the triangle-morphism-extension lemma makes them equal.
This proves quotient-transition coherence, not just objectwise reduction isomorphisms.

8. Identification with the specified exceptional inverse image. At finite level
[lem-exc-closed-ambient] supplies the ambient etale closed adjoint. The ordinary etale open-closed
sequence gives a triangle on all complexes. Exact inverse image, exact closed direct image (a
closed immersion is finite), and open full faithfulness supply the four adjunctions and invertible
counits, and the shift-compatible right-adjoint theorem gives the closed adjoint its exact
structure, so [lem-sf-ordinary-triangle-counit-cone] applies. Open finiteness and the truncation
spectral sequence make its open vertex bounded constructible. The cohomology long exact sequence
expresses each cohomology sheaf of its first vertex as an extension of a kernel by a cokernel of
constructible sheaves; the Serre property gives constructibility, and boundedness follows from the
same sequence. Exact $i^*$ and constructible pullback restrict the closed adjoint. The
compactification $Z\xrightarrow1Z\xrightarrow iX$ gives compact-support direct image $i_*$, hence
the adjoint in the exceptional-inverse-image definition. For a finite pro-etale constructible $K$,
choose its bounded constructible etale origin. Exact comparison pullback and the canonical
direct-image mate identify the middle and open maps of that etale supported triangle with Step 3.
Orthogonality and [lem-weil-pbc-triangle-morphism-extension] (1)-(2) give the unique comparison;
[lem-sf-triangle-morphism-iso] makes it invertible. Applying $i^*$ identifies the exceptional
functors and counits, hence the adjunction units. Step 7 identifies the integral reductions with
these finite objects respecting quotient transitions. Completeness gives $Ri^!K\cong
R\varprojlim_n\operatorname{Res}_nRi_n^!K_n$, the stated integral definition. The Hom bijections
remain those of Step 2.

9. At both the finite and integral stages, $Ri^!$ is an exact functor, linear over the
corresponding coefficient ring. At finite level its $A_{E,n}$-linearity can also be seen directly:
under the adjunction a map $P\to Ri^!K$ is sent to its closed pushforward followed by the counit;
both operations are linear, so the inverse bijection, and the representing action on maps, are
linear. Give it the unique shift structure compatible with the adjunction $i_*\dashv Ri^!$, using
the adjunction shift theorem. The closed functor $i_*$ is exact: on the ambient categories it is a
derived direct image, and the full finite and integral constructible subcategories are
triangulated, and its preservation at each stage was proved above. The
shift-compatible-right-adjoint theorem now makes $Ri^!$ exact. Thus all the functors, units,
counits and triangle maps constructed so far have compatible exact structures; this supplies the
exactness required before scalar localization.

10. Uniqueness of the connecting arrow and of maps of supported triangles, at the finite and
integral stages. Write a supported triangle as
$A\xrightarrow{e}K\xrightarrow{u}B\xrightarrow{\delta}A[1]$, where $A$ is in the closed image and
$B$ in the open direct image. Given $f:K\to K'$, the right-adjoint bijection determines a unique
$a:A\to A'$ with $e'a=fe$. TR3 supplies a map $b:B\to B'$ completing $(a,f)$ to a triangle
morphism. Its first square on $K$ gives $bu=u'f$. The natural map $Rj_*j^*f$ satisfies the same
equation. The difference of the two maps factors through $\delta$ by Hom-out exactness and so is
zero, since $\operatorname{Hom}(A[1],B')=0$. Therefore $b=Rj_*j^*f$, proving functoriality. For
two choices of $\delta$ with fixed $e,u$, TR3 with the two identity maps gives such a $b$; the
same vanishing forces $b=1$, and the last square forces the two connecting arrows to coincide. The
closed map is also unique when only $f$ is specified: its difference factors through $B'[-1]$ by
Hom-into exactness, and $\operatorname{Hom}(A,B'[-1])=0$. This proves exactly the uniqueness
promised by the unit and by (3).

11. Coefficient-category identification before rationalization. On each of X, Z and U, finite type
over the field gives Noetherianity and finite dimension, and ell is invertible. By
[lem-weil-pbc-integral-stratified-perfect-characterization], the full completed-coefficient
category of [def-weil-derived-complete-integral-detailed] is exactly the category of
[def-weil-pbc-bounded-constructible-complete], including the existence of compatible etale-origin
witnesses, with the same completed ring sheaf and reduction functors. Their raw rationalizations
therefore agree, with the same objects and Hom modules tensored with E. Use this identification
also for the finite-stage categories in Step 12. Rational stage. Apply rational transport to the
exact $R$-linear functors and to their units and counits. The identities remain identities, and
the Hom adjunction bijections tensor with $E$, so $i_{*,E}\dashv Ri_E^!$ and $j_E^*\dashv
Rj_{*,E}$. Distinguished integral triangles remain distinguished under raw scalar localization.
Hom orthogonality remains zero after tensoring. For a middle map $f$, the rational adjunction
determines the closed map $a$, and TR3 gives an open map $b$. Subtracting the natural open map
gives a map factoring through the closed vertex shifted by $1$; rational orthogonality makes that
factor zero. Applying this to identity middle and closed maps forces two connecting arrows to
agree, and the underlying objects still have the specified integral representatives. This proves
(1)–(3) at $E$, without an idempotent completion.

12. Coefficient-extension coherence and the algebraically closed stage. For $E\subset L$, scalar
extension commutes with $i_*,Rj_*,i^*,j^*$ by the scalar-extension theorem. It carries the open
unit to the open unit as follows. Write $S$ for coefficient extension and $\pi:S
Rf_{*,E}\xrightarrow{\sim}Rf_{*,L}S$. Under the pullback comparison, the transpose of $\pi
S\eta_{f,K}$ is $S(\varepsilon_f f^*\circ f^*\eta_f)=1$, since $\pi$ is the canonical projection
mate adjoint to $S\varepsilon_f$. Thus $\pi S\eta_f$ is the $L$-unit; its counit equation is
$\varepsilon_{f,L}\circ f_L^*\pi=S\varepsilon_{f,E}$ under that same comparison. This uses the
canonical derived tensor/pullback identification, not an arbitrarily chosen isomorphism of the two
functors. Thus scalar extension of the supported triangle is a triangle with the prescribed middle
and open vertices and maps at $L$. Step 10 gives a unique isomorphism of these supported
triangles; applying $i^*$ gives $Ri_E^!K\otimes_EL\cong Ri_L^!(K\otimes_EL)$, preserving the
counit. Comparing successive extensions with direct extension, both composites preserve this
counit and the middle object, so Step 10 makes them equal. For the unit equation set $L=E$ and use
the identity scalar comparison; both supported comparisons preserve the counit and hence are
identities by Step 10. For the shift equation compare the scalar-extension comparison at $K[1]$
with its shifted comparison at $K$ under the supplied exact shifts. Both have the same middle and
open components, so Step 10 makes their closed components agree too. Exact functors and compatible
transformations now descend by the common-stage descent theorem; the Verdier-axioms theorem keeps
the triangles distinguished. The finite-stage adjunction bijections commute with extension, and
hence induce adjunction bijections on the filtered-colimit Hom groups. Orthogonality passes to
these same colimits. This proves (1)–(3) at $\overline{\mathbf Q}_\ell$ for the specified pair
category.

13. At each stage take $H=Ri^!Rj_*G$. The adjunction and orthogonality give
$\operatorname{Hom}(N,H)=\operatorname{Hom}(i_*N,Rj_*G)=0$ for every $N$; taking $N=H$ makes
$1_H=0$, so $H=0$. Full faithfulness of the closed pushforward gives the isomorphism $Q\to
Ri^!i_*Q$ by the closed-unit theorem. This proves (4).

14. Finite Tor preparation. For $A=A_{E,n}$ and $\kappa=A/(\varpi_E)$, the residue criteria detect
Tor amplitude by the cohomological interval of $-\otimes_A^L\kappa$ on the etale and pro-etale
constructible categories. Every application below is to a bounded constructible object, already
established in Steps 1–4 and 8. Derived pullback is monoidal; the coefficient-ring maps identify
pullback of $\kappa$ with $\kappa$. Exact inverse image therefore preserves the interval of the
residue tensor, so $i^*$ and $j^*$ preserve Tor intervals. They preserve constructibility by the
pullback theorem. The comparison-pullback Tor theorem ensures that an etale origin $G'$ of a
pro-etale finite-Tor $G$ has the same Tor interval, and conversely. In particular these assertions
do not assume that every bounded constructible $A$-complex is perfect.

15. The closed pushforward preserves the same Tor interval. Let $P$ on $Z$ have interval $[a,b]$,
and put $C=i_*P\otimes_A^L\kappa$. Exactness and monoidality of $j^*$ give $j^*C=0$. For each $r$,
the sheaf $\mathcal H^r(C)$ is therefore in the closed image by the essential-image theorem, and
its closed unit identifies it with $i_*i^*\mathcal H^r(C)$. Exactness of $i^*$, its monoidality
and $i^*i_*P\cong P$ give $i^*\mathcal H^r(C)=\mathcal H^r(P\otimes_A^L\kappa)$, which is zero
outside $[a,b]$. Hence $\mathcal H^r(C)=0$ there. Apply the pro-etale residue criterion to the
bounded constructible $i_*P$ (closed constructible preservation is included in the all-stage
closed-unit theorem). This proves finite-level (3′).

16. Uniform etale direct-image bound. Set $N=2d+c$. When $k$ is algebraically closed, $c=0$, so
the etale direct-image vanishing theorem applied to $j$ gives $R^qj_*M=0$ for $q>N$, for every
$A$-module sheaf, with a bound independent of $n$. For a general field with
$\operatorname{cd}_{\mathrm{tor}}(k)\le c$, the same inference has the following explicit
argument: on the basis of affine etale $V\to X$, the scheme $V\times_XU$ is finite type over $k$
and has dimension at most $d$ by etale local-dimension invariance: the local ring at each point
has the dimension of the corresponding local ring on $U$, and the stalk-dimension chain theorem
identifies these local dimensions with the lengths of generalization chains. Taking their supremum
gives the topological dimension bound. The finite-type torsion-cd theorem makes its cohomology
vanish in degrees $>2d+c$. The higher-direct-image sheafification formula then makes $R^qj_*M$
zero on $X$. The forgetful derived-direct-image comparison justifies using the underlying torsion
abelian sheaf in this formula. When $U$ is empty the direct image is zero and $N=c\ge0$ works
directly, with no use of $\dim\varnothing=-\infty$.

17. Open Tor bound. Let $G$ have Tor interval $[a,b]$, and choose its bounded constructible etale
origin $G'$; by Step 14, $G'\otimes_A^L\kappa$ has cohomology only in $[a,b]$. The truncation
spectral sequence, with Step 16's vanishing bound, puts $Rj_*(G'\otimes_A^L\kappa)$ in $[a,b+N]$.
The projection-formula lemma for a finitely presented constant module applies to $f=j$, $K=G'\in
D^-$ and $M=\kappa$: $A$ is Noetherian (indeed Artinian), $\kappa=A/(\varpi_E)$ is finitely
presented by a single relation, and the required uniform bound is Step 16. It gives
$Rj_*G'\otimes_A^L\kappa\cong Rj_*(G'\otimes_A^L\kappa)$. Exact monoidal comparison pullback and
the qcqs direct-image comparison give the same residue interval for $Rj_*G$. This object is
already bounded constructible by Step 1; the residue criterion now gives Tor interval
$[a,b+2d+c]$. This is (1′); the residue field was not treated as a perfect $A$-module.

18. Closed exceptional Tor bound. Let $K$ have Tor interval $[a,b]$. By Steps 14 and 17, $j^*K$
has interval $[a,b]$ and $B=Rj_*j^*K$ interval $[a,b+N]$. Tensor the finite supported triangle
with $\kappa$; exactness of derived tensor leaves it distinguished. The exact cohomology segment
$\mathcal H^{r-1}(B\otimes_A^L\kappa)\to\mathcal H^r(i_*Ri^!K\otimes_A^L\kappa)\to\mathcal
H^r(K\otimes_A^L\kappa)$ is zero on the two outside terms whenever $r<a$ or $r>b+N+1$. Apply the
exact monoidal $i^*$ and $i^*i_*\cong1$ to identify the residue tensor of $Ri^!K$, giving the same
vanishing. Since $Ri^!K$ is bounded constructible by Step 4, the residue criterion gives interval
$[a,b+2d+c+1]$. This proves finite-level (2′).

19. At the integral stage use the definition by a single uniform Tor interval for all reductions.
Steps 5–6 identify reductions of $Rj_*,i_*,i^*,j^*$ with the finite operations; Step 7 identifies
reductions of $Ri^!$. Applying Steps 14–18 at every $n$ gives the same intervals $[a,b]$,
$[a,b+2d+c]$, $[a,b+2d+c+1]$, independent of $n$. Thus (1′)–(3′) hold integrally. The finite-Tor
categories are full triangulated subcategories by their defining finite/integral
triangulated-subcategory theorems, so the supported triangles lie in them, and the adjunction
bijections and (4) restrict to them. At $E$ and $\overline{\mathbf Q}_\ell$ the finite-Tor
categories equal the constructible categories by definition. This proves (4′) and all the
remaining assertions about finite Tor.

20. Weil equivariance. Use the stated descent of the whole closed/open pair over $k_0$. The
Weil-operation theorem supplies Frobenius comparisons for $i_*,i^*,j^*,Rj_*$ and equivariance of
the open unit; all their constructible domains have now been proved. Write $F_K=i_*Ri^!K$. For a
Weil complex $(K,\theta_K)$, pull the supported triangle back by the Frobenius automorphism and
compare it with the supported triangle of $K$. TR3 and Step 10 give the unique map
$\theta_F:g_X^*F_K\to F_K$ extending the given $\theta_K$ and its open counterpart. It is
invertible by two-out-of-three. The induced $i^*\theta_F$, combined with the pullback composition
comparison, gives $\theta_{Ri^!K}:g_Z^*Ri^!K\xrightarrow{\sim}Ri^!K$. The counit is equivariant by
construction. Under the adjunction Hom bijections constructed in Step 2 and identified with the
specified functor in Step 8 this action on the right adjoint is the mate of the action on $i_*$,
so the adjunction bijections commute with Frobenius; in particular the unit, which corresponds to
an identity, is equivariant. Finally Step 10 says the connecting arrow is the unique one
completing the first two arrows, so its Frobenius conjugate is itself. This proves equivariance of
all three arrows and of the exceptional unit.
-/
theorem sfLocalizationAllStages
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : k))
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (X : Scheme.{u}) (t : X ⟶ Spec (.of k))
    [IsSeparated t] [LocallyOfFiniteType t] [QuasiCompact t]
    {Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (hij : Set.range j = (Set.range i)ᶜ) :
    (∀ n : ℕ, Nonempty (SfFiniteLocalization l E n k i j)) ∧
    Nonempty (SfIntegralLocalization l E k hl t i j) ∧
    Nonempty (SfRationalLocalization l E k hl t i j) ∧
    Nonempty (SfAlgebraicallyClosedLocalization l Ω k hl t i j) := by
  sorry

/-- Weil lifts of the supported adjunctions and all three triangle arrows.
Underlying functors and maps are specified, so this asserts equivariance of the
actual triangle; it does not place a triangulation on the category of Weil pairs.
Source: blueprint supported localization, final Weil clause
(blueprint: prop-sf-localization-all-stages). -/
structure SfWeilLocalization
    {C Z U : Type c} [Category.{h} C] [Category.{h} Z] [Category.{h} U]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroMorphisms Z]
    (S : SfSupportedLocalization (𝟭 C) (𝟭 Z) (𝟭 U))
    (ΦX : C ⥤ C) (ΦZ : Z ⥤ Z) (ΦU : U ⥤ U) where
  exceptionalLift : Endofunctor.IsoAlgebra ΦX ⥤ Endofunctor.IsoAlgebra ΦZ
  closedLift : Endofunctor.IsoAlgebra ΦZ ⥤ Endofunctor.IsoAlgebra ΦX
  openPullLift : Endofunctor.IsoAlgebra ΦX ⥤ Endofunctor.IsoAlgebra ΦU
  openPushLift : Endofunctor.IsoAlgebra ΦU ⥤ Endofunctor.IsoAlgebra ΦX
  shiftLift : Endofunctor.IsoAlgebra ΦX ⥤ Endofunctor.IsoAlgebra ΦX
  exceptional_underlying : exceptionalLift ⋙ Endofunctor.IsoAlgebra.forget ΦZ =
    Endofunctor.IsoAlgebra.forget ΦX ⋙ S.exceptional
  closed_underlying : closedLift ⋙ Endofunctor.IsoAlgebra.forget ΦX =
    Endofunctor.IsoAlgebra.forget ΦZ ⋙ S.iPush
  open_pull_underlying : openPullLift ⋙ Endofunctor.IsoAlgebra.forget ΦU =
    Endofunctor.IsoAlgebra.forget ΦX ⋙ S.jPull
  open_push_underlying : openPushLift ⋙ Endofunctor.IsoAlgebra.forget ΦX =
    Endofunctor.IsoAlgebra.forget ΦU ⋙ S.jPush
  shift_underlying : shiftLift ⋙ Endofunctor.IsoAlgebra.forget ΦX =
    Endofunctor.IsoAlgebra.forget ΦX ⋙ shiftFunctor C (1 : ℤ)
  closedAdjunction : closedLift ⊣ exceptionalLift
  openAdjunction : openPullLift ⊣ openPushLift
  counit_underlying (K : Endofunctor.IsoAlgebra ΦX) :
    HEq ((Endofunctor.IsoAlgebra.forget ΦX).map (closedAdjunction.counit.app K))
      (S.exceptionalAdjunction.counit.app K.carrier)
  open_unit_underlying (K : Endofunctor.IsoAlgebra ΦX) :
    HEq ((Endofunctor.IsoAlgebra.forget ΦX).map (openAdjunction.unit.app K))
      (S.openAdjunction.unit.app K.carrier)
  closed_unit_underlying (Q : Endofunctor.IsoAlgebra ΦZ) :
    HEq ((Endofunctor.IsoAlgebra.forget ΦZ).map (closedAdjunction.unit.app Q))
      (S.exceptionalAdjunction.unit.app Q.carrier)
  boundaryLift : openPullLift ⋙ openPushLift ⟶ exceptionalLift ⋙ closedLift ⋙ shiftLift
  boundary_underlying (K : Endofunctor.IsoAlgebra ΦX) :
    HEq ((Endofunctor.IsoAlgebra.forget ΦX).map (boundaryLift.app K))
      (S.boundary.app K.carrier)

/-- The actual geometric-fibre morphism induced by a morphism over the finite field.
Source: blueprint supported localization, Weil descent condition
(blueprint: prop-sf-localization-all-stages). -/
def sfLocalizationFiberMap (D : FiniteFieldDatum.{u})
    {Y₀ X₀ : Over (Spec (.of D.k₀))} (f : Y₀ ⟶ X₀) :
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj Y₀).left ⟶
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj X₀).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f).left

/-- Weil-equivariant supported localization, with the closed/open pair itself
obtained by base change from the finite field, and with the current fixed-pair
Weil categories. The lifts carry exactly the actual underlying adjunction maps.
Source: Weil blueprint, supported localization, final paragraph
(blueprint: prop-sf-localization-all-stages).
Proof: the immersion pair commutes with geometric Frobenius. Apply the canonical
pullback/direct-image comparisons to the four adjunctions. Their mates identify
the Frobenius pullback of the closed right adjoint with the right adjoint of the
Frobenius pullback. Uniqueness of adjoints gives the coefficient-compatible
exceptional comparison. The mate equations make the exceptional counit, open
unit, and exceptional unit equivariant. Pull back the distinguished triangle;
its first two arrows are those same equivariant maps. Closed-to-open orthogonality
and uniqueness of the connecting arrow identify the pulled-back boundary with
the original boundary. Thus all three arrows and the unit are morphisms of the
fixed pairs. Repeat after rationalization and common-stage descent; the specified
scalar comparisons respect units, counits and the boundary. No triangulated
structure on fixed pairs is asserted. -/
theorem sfLocalizationAllStages_weil
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (X₀ Z₀ U₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    (i₀ : Z₀ ⟶ X₀) (j₀ : U₀ ⟶ X₀)
    [IsClosedImmersion i₀.left] [IsOpenImmersion j₀.left]
    (hij : Set.range j₀.left = (Set.range i₀.left)ᶜ) :
    (∃ S : SfSupportedLocalization
        (𝟭 (sfRationalConstructibleCategory l E (D.geometricFiber X₀).left))
        (𝟭 (sfRationalConstructibleCategory l E (D.geometricFiber Z₀).left))
        (𝟭 (sfRationalConstructibleCategory l E (D.geometricFiber U₀).left)),
      S.iPull = @rationalDerivedPullback l _ E _ _ _ _ _ (sfLocalizationFiberMap D i₀)
        (sfWeilPrimeInvertible D l hl Z₀) (sfWeilPrimeInvertible D l hl X₀) ∧
      S.jPull = @rationalDerivedPullback l _ E _ _ _ _ _ (sfLocalizationFiberMap D j₀)
        (sfWeilPrimeInvertible D l hl U₀) (sfWeilPrimeInvertible D l hl X₀) ∧
      Nonempty (SfWeilLocalization S
        (sfWeilFrobeniusPullback D l hl X₀ E) (sfWeilFrobeniusPullback D l hl Z₀ E)
        (sfWeilFrobeniusPullback D l hl U₀ E))) ∧
    (∃ S : SfSupportedLocalization
        (𝟭 (generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left))
        (𝟭 (generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Z₀).left))
        (𝟭 (generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber U₀).left)),
      S.iPull = @commonStageDerivedPullback l _ Ω _ _ _ _ _ (sfLocalizationFiberMap D i₀)
        (sfWeilPrimeInvertible D l hl Z₀) (sfWeilPrimeInvertible D l hl X₀) ∧
      S.jPull = @commonStageDerivedPullback l _ Ω _ _ _ _ _ (sfLocalizationFiberMap D j₀)
        (sfWeilPrimeInvertible D l hl U₀) (sfWeilPrimeInvertible D l hl X₀) ∧
      Nonempty (SfWeilLocalization S
        (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω)
        (sfCommonStageWeilFrobeniusPullback D l hl Z₀ Ω)
        (sfCommonStageWeilFrobeniusPullback D l hl U₀ Ω))) := by
  sorry

end WeilConjectures
