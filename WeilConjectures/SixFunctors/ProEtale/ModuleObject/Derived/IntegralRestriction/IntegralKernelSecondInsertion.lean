/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelSecondPullSection
import all WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondDiagonalInsertionFactor
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # Integral second diagonal insertion -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
open DiagonalCoefficients RationalP1
set_option allowUnsafeReducibility true in
attribute [local reducible] traceTate
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] twist projectionMap singleUnitIso

set_option maxHeartbeats 1600000 in
-- Keep the fixed native tensor comparisons folded during the insertion calculation.
/-- The integral diagonal insertion is the forward projection of the scalar class.
Source: sk-thm-int-restriction-line.proof.md, paragraph (1), second triangle.
(blueprint: lem-integral-kernel-second-insertion).
Proof: the canonical integral comparison between the two pulled-back twisted
objects satisfies the diagonal section equation. Apply the coefficient-independent
insertion factorization to this comparison and the supplied integral family.
Unfold the literal forward projection and the two fixed native tensor bundles.
Associativity identifies its two final factors with the forward projection. -/
theorem integralKernel_second_insertion
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (Y : Scheme.{u})
    [∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x)]
    (family : Family l Y)
    (K : DerivedCategory (Modules (Profinite.padicIntegersRingObj l E.val) Y)) :
    let Λ := Profinite.padicIntegersRingObj l E.val
    let L := fun X : Scheme.{u} ↦ spIntegralTwist X l E
    let d := family.integral E
    let M := (twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj
      ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K)
    (pushSectionIso Λ Y).hom.app M ≫
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
        (diagonalClassMap Λ Y L d M) =
    (ρ_ M).inv ≫
      (M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫ d.support₂.hom ≫
        d.R₂.R.map d.delta ≫
        (secondDiagramPushIso Λ Y L d).hom.app (traceTate l E (diagonalSurface Y)))) ≫
      integralSecondForwardProjection l E Y K := by
  dsimp only
  have hi := diagonal_insertion_from_section
    (Profinite.padicIntegersRingObj l E.val) Y (fun X ↦ spIntegralTwist X l E)
    (family.integral E)
    ((twist (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y)
      (spIntegralTwist (ProjectiveLine Y) l E)).obj
        ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj l E.val)
          (ProjectiveLine Y ↘ Y)).obj K))
    (integralSecondPullComparison l E Y K).inv
    (integralKernel_second_pull_section l E Y K)
  unfold integralSecondForwardProjection
  unfold internalMonoidal internalTensorBundle nativeTensorBundle at hi ⊢
  simpa only [traceTate, Category.assoc] using hi

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
