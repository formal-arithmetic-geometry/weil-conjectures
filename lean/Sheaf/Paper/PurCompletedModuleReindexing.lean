/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.Paper.PurCompletedReindexingData

/-! # PurCompletedModuleReindexing

Source: Stacks Project and the extracted proof of
lem-pur-isomorphism-completed-reduction-reindexing.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.privateModule false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] completedAdicChangeData completedReductionCoefficient
attribute [local irreducible] proEtaleRingModulePullback
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients
attribute [local instance 2000] reductionModulesHasDerivedCategory reductionTowerHasDerivedCategory
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The tensor pullback is sectionwise reindexing on completed-ring modules, and
reverse pullback is its specified inverse.
Source: extracted proof, step 1; Stacks Tags 09A5, 00WX and 03D2.
(blueprint: lem-pur-completed-module-section-reindexing).
Proof: postcomposition with u and its inverse gives inverse covering-preserving
site equivalences. The comma-normalized inverse-image identification evaluates a
section by the inverse-image unit followed by the canonical comma restriction.
The completed coefficient isomorphism transports the action by its inverse; its
composition identity identifies reverse transport with the coefficient map for
inv u. The tensor-unit-normalized adjunction identifies this transport with the
published tensor pullback. Transporting the comma formula through that adjunction
gives the displayed section equation. The identity and composition equations for
completed coefficients give the unit and counit of the module equivalence; both
are natural in restrictions and module morphisms. Thus the inverse functor is the
published pullback along inv u, with the stated literal functor equalities. -/
theorem purCompletedModuleReindexing
    {T' T : Scheme.{t}} (u : T' ⟶ T) [IsIso u] :
  PurCompletedReindexingAtSections d u ∧
  PurCompletedReindexingAtModules d u := by sorry

end AlgebraicGeometry.Scheme
