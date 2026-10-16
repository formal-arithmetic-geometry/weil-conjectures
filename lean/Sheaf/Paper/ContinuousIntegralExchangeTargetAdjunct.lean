/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Paper.ContinuousIntegralComparisons

/-! # Coherence of integral localization and the specified exchange map -/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

/-- Normal form for the target side after the bounded f′ adjunction.
Source: Bhatt--Scholze, Remark 6.8.15; ChangeOfCoefficients.lean derived comparisons
and the specified unit-square-counit exchange construction.
(blueprint: lem-weil-pbc-continuous-integral-exchange-target-adjunct).

Proof. Apply the bounded f′ adjunction to the target composite. Counit naturality moves the g′
pull comparison past the f′ counit. The mate/counit identity replaces the f′ push comparison.
Naturality of the inverse f′ pull comparison moves scalar extension of integral exchange past
it. Expand the integral exchange adjunct and use naturality of the g′ pull comparison. Coherence
of the specified pull comparisons with composition, obtained by right deriving the
restriction/pushforward composition diagram and conjugating through adjunctions, gives the pull
square cube. Precompose that cube with inverse f′ pull comparison and postcompose with g′
pullback of inverse f pull comparison. Cancel these two isomorphisms and postcompose with scalar
extension of the integral counit. This is the displayed composite. No push comparison or
exchange is inverted. -/
theorem integralConstructible_exchange_target_adjunct
    (sq : CommSq g' f' f g) (K : integralConstructible ℓ E X) :
    ((boundedConstructibleUpperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj E) ℓ k f').homEquiv _ _).symm
      ((integralScalarConstructible ℓ E Y').map
          ((boundedConstructibleBaseChange (integralCoeff ℓ E) ℓ k sq).app K) ≫
        integralConstructibleTargetHom ℓ E k f' g' K) =
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k f').map
        (integralConstructiblePullHom ℓ E k g
          ((boundedConstructibleLowerStar (integralCoeff ℓ E) ℓ k f).obj K)) ≫
      (boundedConstructiblePullbackSquareComparison
        (Profinite.continuousMapRingObj E) ℓ k sq).hom.app
          ((integralScalarConstructible ℓ E Y).obj
            ((boundedConstructibleLowerStar (integralCoeff ℓ E) ℓ k f).obj K)) ≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g').map
        (integralConstructiblePullIso ℓ E k f
          ((boundedConstructibleLowerStar (integralCoeff ℓ E) ℓ k f).obj K)).inv ≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g').map
        ((integralScalarConstructible ℓ E X).map
          ((boundedConstructibleUpperStarLowerStarAdjunction
            (integralCoeff ℓ E) ℓ k f).counit.app K)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
