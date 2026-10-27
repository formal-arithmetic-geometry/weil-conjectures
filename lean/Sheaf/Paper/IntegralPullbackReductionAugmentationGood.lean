/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C6
-/
module

public import Sheaf.Paper.IntegralOrdinaryPullbackComparison
public import Sheaf.Paper.CompletedPullbackTowerRealizations

/-! # Good-representative reduction/pullback augmentation

This is the representative-level part of the coherent reduction mate. It is
separated from the localization descent statement so that the construction can
be proved independently on flat-term K-flat representatives.
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

/-- The normalized pullback/reduction adjunct equation on good representatives.
Source: Stacks 03D2, 07A6, 08TC and 0941; the representative calculation in
`fix-prop-projection-formula.proof.md`.
(blueprint: lem-sf-pullback-reduction-augmentation-good).

Proof: choose simultaneous flat-term K-flat representatives. The ordinary
pullback comparison and the strict Roos realization have the same finite
projection maps. The quotient units and transition maps therefore agree on the
representative; product and mapping-cocone extensionality identify the resulting
chain maps. The reduction/limit adjunction then gives the displayed equation at
every object in the good localization.
-/
theorem pullbackReductionAugmentation_good {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ a : PurCompactSupport.pull (PurCompactSupport.completed l E) f ⋙
        (pullbackTensorCalculus l E X).reduction ≅
      (pullbackTensorCalculus l E Y).reduction ⋙ pullbackTensorSequenceDerived l E f,
      ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        (pullComparison l E f).app (DerivedCategory.Q.obj P.obj) ≫
            (pullbackTensorIntegralPullbackModel l E f).hom.app (DerivedCategory.Q.obj P.obj) =
          (pullbackTensorCalculus l E X).adjunction.unit.app
              ((PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj
                (DerivedCategory.Q.obj P.obj)) ≫
            (coefficientSequenceLimit l E X).map
              (a.hom.app (DerivedCategory.Q.obj P.obj)) := by
  sorry

end WeilConjectures.IntegralOrdinary
