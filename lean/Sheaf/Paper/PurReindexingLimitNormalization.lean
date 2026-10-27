/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.Paper.PurCompletedReindexingData

/-! # PurReindexingLimitNormalization

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

/-- Reindexing commutes with the derived strict limit, preserving projections,
K-injective comparison units and the actual quotient augmentation.
Source: extracted proof, steps 3 and 5; Stacks Tags 0A07 and 099N.
(blueprint: lem-pur-reindexing-limit-unit-normalization).
Proof: the completed-module equivalence has exact reverse reindexing as left
adjoint. Its termwise tower functor therefore preserves K-injectives. Preservation
of limits supplies beta; its composites with the limit projections are the
reindexed original projections. Apply beta on K-injective tower resolutions to
obtain b. The right-derived universal property descends the comparison and its
inverse, and its unit equation is the displayed representative formula. For the
constant-tower unit, both routes factor the same compatible family of reindexed
resolution maps through the inverse limit; projection uniqueness makes them equal.
Naturality for the strict quotient augmentation then identifies its composite
with the specified ordinaryToCompleted, giving the last equation for every K.
This last step concerns the actual quotient augmentation, not its finite-level
images; no derived-completeness hypothesis is needed for that equality. -/
theorem purReindexingLimitNormalization
    {T' T : Scheme.{t}} (u : T' ⟶ T) [IsIso u] :
  (∃ beta : completedTowerLimit T (d.completedRing T) ⋙
      proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u) ≅
      d.towerModulePull u ⋙ completedTowerLimit T' (d.completedRing T'),
    (∀ (C : d.towers T) (n : ℕᵒᵖ),
      beta.hom.app C ≫ limit.π ((d.towerModulePull u).obj C) n =
        (proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u)).map (limit.π C n)) ∧
    ∃ b : completedRlim T (d.completedRing T) ⋙ d.pull u ≅
      d.towerPull u ⋙ completedRlim T' (d.completedRing T'),
    (∀ I : CochainComplex (d.towers T) ℤ, I.IsKInjective →
      (d.pull u).map ((completedTowerLimit T (d.completedRing T)).rightDerivedFunctorUnitQ I) ≫
        b.hom.app (DerivedCategory.Q.obj I) ≫
        (completedRlim T' (d.completedRing T')).map
          ((d.towerModulePull u).mapDerivedCategoryFactors.hom.app I) =
      (proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u)).mapDerivedCategoryFactors.hom.app
          (((completedTowerLimit T (d.completedRing T)).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex beta.hom (.up ℤ)).app I) ≫
        (completedTowerLimit T' (d.completedRing T')).rightDerivedFunctorUnitQ
          (((d.towerModulePull u).mapHomologicalComplex (.up ℤ)).obj I)) ∧
    (∀ K : d.derived T,
      d.ordinaryToCompleted u K =
        (d.pull u).map (d.completionUnit T K) ≫
          b.hom.app ((completedReductionTower T d).obj K))) := by sorry

end AlgebraicGeometry.Scheme
