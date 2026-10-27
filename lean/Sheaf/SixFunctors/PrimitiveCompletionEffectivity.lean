/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T7
-/
module

public import Sheaf.SixFunctors.GeneratorReductionData
import Sheaf.SixFunctors.FiniteTorOrdinaryTensorComplete
import Sheaf.SixFunctors.FiniteTorOrdinaryPullComplete
import all Sheaf.SixFunctors.OpenReconstructionEffectivity
import Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus
import Sheaf.Paper.RoosIntrinsicCompletenessEquivalence
import all Sheaf.Paper.IntegralDerivedOperationsOnSlices
import all Sheaf.Paper.ConstantCoefficientObjectsConstructible

/-! # Primitive completion effectivity

Source: current blueprint fix-prop-coherence, primitive realization step.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u s i
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem input_complete (X : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l E X))
    (hK : finiteTorConstructibleIntegral l E X K ∨
      K = (IntegralSystemRealization.calculus l E X).integralClosed.monoidal.tensorUnit) :
    IntegralOnSlice.IsComplete l E X none K := by
  rcases hK with hK | rfl
  · obtain ⟨D, hl⟩ := exists_coefficientTestDatum l
    exact ⟨D, hl, (sfDerivedComplete_iff_legacy l E X D hl K).mp hK.1.1⟩
  · exact tensorUnit_complete l E X

private theorem completion_unit_isIso (X : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l E X))
    (hK : IntegralOnSlice.IsComplete l E X none K) :
    IsIso ((IntegralOnSlice.completionUnit l E X none).app K) := by
  classical
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd, _⟩ := PrincipalKoszulStrictReplacement.coefficient_datum l E
  let := IntegralOnSlice.goodLocalization l E X none
  let L := IntegralOnSlice.qGood l E X none
  let W := (HomologicalComplex.quasiIso (IntegralOnSlice.Mod l E X none) (.up ℤ)).inverseImage
    (IntegralOnSlice.Good l E X none).ι
  let : L.EssSurj := Localization.essSurj L W
  let P := L.objPreimage K
  let e : DerivedCategory.Q.obj P.obj ≅ K := L.objObjPreimageIso K
  exact ((roosIntrinsicCompletenessEquivalence p l (by omega) E X d hd K P e).out 0 4).mp hK

/-- Primitive completion units on the complete constructible finite-Tor domain,
including the scalar unit as a separate allowed input.
Source: blueprint fix-prop-coherence, maps-used sentence and generator realization
Step 3; Bhatt--Scholze Lemma 6.5.5; Stacks 099N and 0941
(blueprint: lem-sf-primitive-completion-effectivity).

Proof: present each input by a flat-term K-flat quotient complex. For tensor,
constructible finite-Tor inputs have bounded finite-projective models after a finite
constructible stratification. Their ordinary total tensor is complete: the quotient
augmentation is invertible on each bounded projective model, and the open-closed
triangles descend this assertion from the strata. Its actual Roos augmentation is
Tensor.chi by the two coordinates in Tensor.canonical. For pullback, inverse image
of the finite-projective models remains bounded finite-projective; its quotient
tower is the tower fixed by Pull.model and Pull.generators. The actual completion
unit is therefore invertible on the ordinary pullback. For the scalar unit, use
its own rank-one free model in both arguments. Finally complete reconstruction
makes the reduction/total-limit adjunction unit invertible at either kind of input:
its reduction is invertible by the triangle identities and normalized effectivity,
and derived Nakayama on the complete source and complete target gives the claim.
These arguments identify the specified maps before localization, including their
quotient transitions; they do not infer equality from derived evaluations. -/
theorem primitiveCompletionEffectivity (o : Operations l E) :
    (∀ (X : Scheme.{u})
      (K L : DerivedCategory (scalarReductionSource l E X)),
      (finiteTorConstructibleIntegral l E X K ∨
        K = (IntegralSystemRealization.calculus l E X).integralClosed.monoidal.tensorUnit) →
      (finiteTorConstructibleIntegral l E X L ∨
        L = (IntegralSystemRealization.calculus l E X).integralClosed.monoidal.tensorUnit) →
      IsIso ((tensorCompletion l E o X).app (K, L))) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      IsSeparated f → LocallyOfFiniteType f → QuasiCompact f →
      ∀ K : DerivedCategory (scalarReductionSource l E Y),
      (finiteTorConstructibleIntegral l E Y K ∨
        K = (IntegralSystemRealization.calculus l E Y).integralClosed.monoidal.tensorUnit) →
      IsIso (((o.ringed.pull f).unit l E).app K)) ∧
    (∀ (X : Scheme.{u}) (K : DerivedCategory (scalarReductionSource l E X)),
      (finiteTorConstructibleIntegral l E X K ∨
        K = (IntegralSystemRealization.calculus l E X).integralClosed.monoidal.tensorUnit) →
      IsIso ((IntegralSystemRealization.calculus l E X).adjunction.unit.app K)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X K L hK hL
    have hT : IntegralOnSlice.IsComplete l E X none
        ((IntegralSystemRealization.calculus l E X).integralClosed.tensor.obj (K, L)) := by
      rcases hK with hK | rfl
      · rcases hL with hL | rfl
        · exact finiteTorOrdinaryTensorComplete l E X K L hK hL
        · exact complete_of_iso l E X
            ((IntegralSystemRealization.calculus l E X).integralClosed.monoidal.rightUnitor K).symm
            (input_complete l E X K (Or.inl hK))
      · exact complete_of_iso l E X
          ((IntegralSystemRealization.calculus l E X).integralClosed.monoidal.leftUnitor L).symm
          (input_complete l E X L hL)
    have hordinary : IntegralOnSlice.IsComplete l E X none
        ((o.ringed.tensor X).ordinary.tensor.obj (K, L)) := by
      rw [o.ringed.tensorClosed X]
      exact hT
    have := completion_unit_isIso l E X _ hordinary
    change IsIso ((IntegralOnSlice.completionUnit l E X none).app
      ((o.ringed.tensor X).ordinary.tensor.obj (K, L)) ≫
        (o.ringed.tensor X).comparison.hom.app (K, L))
    infer_instance
  · intro X Y f hs ht hq K hK
    have := completion_unit_isIso l E X _
      (finiteTorOrdinaryPullComplete l E f hs ht hq K hK)
    change IsIso ((IntegralOnSlice.completionUnit l E X none).app
      ((IntegralSystemRealization.ringedPull l E f).obj K) ≫
        (o.ringed.pull f).comparison.hom.app K)
    infer_instance
  · intro X K hK
    exact (purNormalizedReconstructionOfScheme l E X
      (IntegralSystemRealization.calculus l E X)).2 K (input_complete l E X K hK)

end WeilConjectures.GeneratorReduction
