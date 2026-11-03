/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Brown.BrownHypothesesDefinitions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientFlatModel
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientReductionFlatModel

import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
import Mathlib.Topology.Category.Profinite.AsLimit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.ProperBaseChange.ProfiniteTestObjectFunctor
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Opposites
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarAssociatorConjugate
import WeilConjectures.CategoryTheory.Derived.DerivedExactSquareComposition
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteNormalizedScalarRestriction
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingTensorTor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTowerMonoidal
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import WeilConjectures.CategoryTheory.DerivedConjugateNormalization
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsAdjunctionQh
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidalComp
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidalComp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

/-!
# Coefficient derived-system evaluation calculus

This module states the native coefficient extension/restriction, tensor--Hom,
evaluation, transitivity, and finite flat-model clauses.
Source: blueprint `det-def-sfb-bounded-constructible.md` and
`det-prop-scalar-six-tensor-hom.md` (blueprint tag:
`lem-coef-derived-system-evaluation-calculus`).
The proof follows six steps: construct derived tensor and closed Hom; use the
canonical `Mod` adjunction; identify the tensorator and Hom bijections; form the
evaluation mate and verify coherence; prove scalar transitivity; and pass to
finite quotient flat models and reductions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.MonoidalClosed
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance 30000] brownHypothesesCondensedMonoidal
  brownHypothesesCondensedBraided brownHypothesesSheafMonoidal brownHypothesesSheafBraided
  brownHypothesesCoefficientMonObj brownHypothesesModuleMonoidalClosed
attribute [local instance] DerivedCategory.braidedCategory'
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

/-- Native ordinary unbounded module derived category. Source: det-def-sfb-derived-categories
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
abbrev NativeScalarCategory (Λ : ScalarSixRing.{u}) (W : Scheme.{u}) :=
  DerivedCategory (ModuleRingedComparison.internalModules Λ.X W)

/-- Left evaluation is the native tensor--Hom counit. Source: det-def-sfb-derived-tensor-hom
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def nativeScalarEvaluation (Λ : ScalarSixRing.{u}) (W : Scheme.{u})
    (K M : NativeScalarCategory Λ W) :
    K ⊗ ((derivedHom Λ.X W).obj (.op K)).obj M ⟶ M :=
  (derivedTensorHomAdjunction Λ.X K).counit.app M

section ClosedHelpers
universe u₁ v₁ u₂ v₂
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
open MonoidalClosed Functor.LaxMonoidal Functor.OplaxMonoidal
variable [MonoidalCategory C] [MonoidalClosed C] [MonoidalCategory D] [MonoidalClosed D]
omit [MonoidalCategory C] [MonoidalClosed C] [MonoidalCategory D] [MonoidalClosed D] in
end ClosedHelpers

section IdentityHelpers

open Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

section AbstractIdentity
universe v w
variable {C : Type v} [Category.{w + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{w + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]

omit [Abelian.HasFunctorialFlatResolution C] in
end AbstractIdentity

set_option maxHeartbeats 3000000 in
-- Comparing the canonical localized adjunction expands the native module instances.
end IdentityHelpers

section FiniteHelpers
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E] [Algebra (Padic ell) E]
  [FiniteDimensional (Padic ell) E] (m n : ℕ) (hmn : m ≤ n) (W : Scheme.{u})
end FiniteHelpers

set_option maxHeartbeats 3000000 in
-- Canonical derived functors have large typeclass parameters.
end AlgebraicGeometry.ProEtale.CondensedRing
