/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.Paper.IntegralComparisonSequenceSystems
public import Sheaf.Paper.CompletedPrimitiveCounitComparison
public import Sheaf.Paper.ProEtaleCoefficientModulePullbackComposition

/-! # Ordinary evaluation of the normalized pullback compositor

Source: Stacks Project, sites-modules.tex, Tag 03D8; the finite normalization
in steps 1 and 3 of lem-pur-normalized-pullback-composition-transport.
(blueprint: lem-pur-ordinary-pullback-composition-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
attribute [local implicit_reducible] WeilConjectures.PrimitiveCounit.inverse
  WeilConjectures.PrimitiveCounit.direct WeilConjectures.PrimitiveCounit.ringMap
  WeilConjectures.PrimitiveCounit.ringComponent WeilConjectures.PrimitiveCounit.base
namespace WeilConjectures.PullbackCompositionTransport

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The given unit-normalized evaluation, with the canonical system functor named
in its type to avoid repeated conversion of the direct-image presentations.
Source: Stacks 03D8; the primitive unit characterization
(blueprint: lem-pur-ordinary-pullback-composition-evaluation). -/
def ordinaryEvaluation {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    integralComparisonSequencePullback l E f ⋙ coefficientSequenceEvaluation l E X n ≅
      coefficientSequenceEvaluation l E Y n ⋙ integralOperationsLevelPullback l E f n :=
  PrimitiveCounit.inverseEvaluation l E f n

/-- Ordinary evaluation respects the two adjunction-normalized compositors.
Source: Stacks Project, sites-modules.tex, Tag 03D8; parent proof steps 1 and 3.
(blueprint: lem-pur-ordinary-pullback-composition-evaluation).
Proof: transpose each composite under the finite inverse-image/direct-image
adjunctions. The defining unit equations for inverseEvaluation identify the
transposed evaluation comparisons with the identities on evaluated direct images.
The defining mate equations for the system and finite compositors identify the
remaining maps with their direct-image fibre-product pasting maps. On a section
at (n,U), both maps are restriction along the same canonical isomorphism
Z x_X (X x_Y U) -> Z x_Y U. Their coefficient actions agree since each
constant-section map sends a scalar to its constant section. The maps agree on
all sections, hence as module-sheaf maps; injectivity of the adjunction Hom
equivalences gives the displayed equality. This works for every strict system M,
with arbitrary transition maps, and for n=0 (the first positive quotient). -/
theorem ordinaryCompositionEvaluation {X Y Z : Scheme.{t}}
    (h : Z ⟶ X) (f : X ⟶ Y) (n : ℕ) (M : coefficientSequenceModules l E Y) :
    (ordinaryEvaluation l E (h ≫ f) n).inv.app M ≫
      (coefficientSequenceEvaluation l E Z n).map
        ((integralComparisonSequenceComposition l E h f).hom.app M) =
    (Scheme.coefficientModulePullbackComposition h f
      (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (n + 1))))).hom.app
          ((coefficientSequenceEvaluation l E Y n).obj M) ≫
      (integralOperationsLevelPullback l E h n).map
        ((ordinaryEvaluation l E f n).inv.app M) ≫
      (ordinaryEvaluation l E h n).inv.app
        ((integralComparisonSequencePullback l E f).obj M) := by sorry

end WeilConjectures.PullbackCompositionTransport
