/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralOrdinaryPullbackComparison
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralPullbackReductionAugmentationGood
import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralPullbackReductionAugmentationDescent

/-! # The coherent reduction mate of ordinary pullback

No tensor comparison occurs here.

## References

* [Stacks, Tag 03D2]
* [Stacks, Tag 07A6]
* [Stacks, Tag 08TC]
* [Stacks, Tag 0941]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOrdinary
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Ordinary inverse image commutes with coherent derived reduction. Its adjunct is
exactly the recorded forward pullback augmentation in the normalized limit model. -/
theorem pullbackReductionAugmentation_exists {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ a : PurCompactSupport.pull (PurCompactSupport.completed l E) f ⋙
        (pullbackTensorCalculus l E X).reduction ≅
      (pullbackTensorCalculus l E Y).reduction ⋙ pullbackTensorSequenceDerived l E f,
      ∀ K : DerivedCategory (integralTowerModules l E Y),
        (pullComparison l E f).app K ≫
            (pullbackTensorIntegralPullbackModel l E f).hom.app K =
          (pullbackTensorCalculus l E X).adjunction.unit.app
              ((PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj K) ≫
            (coefficientSequenceLimit l E X).map (a.hom.app K) := by
  obtain ⟨a, ha⟩ := pullbackReductionAugmentation_good l E f
  exact ⟨a, pullbackReductionAugmentation_of_good l E f a ha⟩

/-- An adjunction determines the coherent inverse-image comparison from its adjunct. -/
theorem pullbackReductionAugmentation_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! a : PurCompactSupport.pull (PurCompactSupport.completed l E) f ⋙
        (pullbackTensorCalculus l E X).reduction ≅
      (pullbackTensorCalculus l E Y).reduction ⋙ pullbackTensorSequenceDerived l E f,
      ∀ K : DerivedCategory (integralTowerModules l E Y),
        (pullComparison l E f).app K ≫
            (pullbackTensorIntegralPullbackModel l E f).hom.app K =
          (pullbackTensorCalculus l E X).adjunction.unit.app
              ((PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj K) ≫
            (coefficientSequenceLimit l E X).map (a.hom.app K) := by
  obtain ⟨a, ha⟩ := pullbackReductionAugmentation_exists l E f
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ((pullbackTensorCalculus l E X).adjunction.homEquiv _ _).injective
  simpa only [Adjunction.homEquiv_unit] using (hb K).symm.trans (ha K)

/-- The unique unit-preserving coherent reduction/pullback comparison. -/
def pullbackReductionComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (pullbackReductionAugmentation_existsUnique l E f).exists.choose

end WeilConjectures.IntegralOrdinary
