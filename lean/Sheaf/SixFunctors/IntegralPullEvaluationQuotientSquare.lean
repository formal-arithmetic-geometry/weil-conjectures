/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.IntegralSystemOperations
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The pullback evaluation quotient square

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 03DI and 0941
(blueprint: lem-sf-integral-pull-evaluation-quotient-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Pullback evaluation respects adjacent quotient transitions, with the scalar
comparison obtained by transposing the published restricted direct-image map.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 0941 and 07A7
(blueprint: lem-sf-integral-pull-evaluation-quotient-square).

Proof: express both transitions on strict cochain representatives by horizontal
restriction on the sequence site. The ordinary evaluation/pullback map is the
mate of the identity on direct-image sections. The scalar-restriction/direct-image
comparison is also the identity on sections. Its mate is therefore precisely the
restriction/pullback comparison appearing here. At every component both routes
apply the same coefficient quotient to a pulled-back section. The equality is
compatible with differentials and hence descends through exact localization.
The normalization of pullbackTensorDerivedEvaluation fixes the localized map;
the K-injective normalization of sfDerivedImageRestriction fixes its mate.
Consequently the identity holds for every derived system, without any inference
from equality at evaluations. Zero objects and n = 0 use the same section formula;
no coefficient-flatness or normalization of the input is needed. -/
theorem integralPullEvaluation_quotientSquare {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ)
    (r : normalizedDVRRes l E X (Nat.le_succ n) ⋙
        proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 2)) ≅
      proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        normalizedDVRRes l E Y (Nat.le_succ n))
    (hr : HEq r
      (sfDerivedImageRestriction f (Padic.coefficientExtensionTransition l E (n + 1))))
    (M : System l E Y) :
    (coefficientSequenceDerivedTransition l E X (Nat.le_succ n)).app ((pull l E f).obj M) ≫
      (normalizedDVRRes l E X (Nat.le_succ n)).map
        ((pullbackTensorDerivedEvaluation l E f n).hom.app M) =
    (pullbackTensorDerivedEvaluation l E f (n + 1)).hom.app M ≫
      (finiteDerivedPullback l E (n + 1) f).map
        ((coefficientSequenceDerivedTransition l E Y (Nat.le_succ n)).app M) ≫
      ((mateEquiv (finiteAdj l E f n) (finiteAdj l E f (n + 1))).symm
        (TwoSquare.mk _ _ _ _ r.inv)).app
        ((coefficientSequenceDerivedEvaluation l E Y n).obj M) := by sorry

end WeilConjectures.IntegralSystemRealization
