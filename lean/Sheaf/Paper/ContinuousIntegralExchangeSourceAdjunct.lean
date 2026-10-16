/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Paper.ContinuousIntegralComparisons
import Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse
import Sheaf.Paper.ContinuousIntegralScalarExact

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

/-- Normal form for the source side after the bounded f′ adjunction.
Source: Bhatt--Scholze, Remark 6.8.15; ChangeOfCoefficients.lean derived comparisons
and the specified unit-square-counit exchange construction.
(blueprint: lem-weil-pbc-continuous-integral-exchange-source-adjunct).

Proof. Apply the bounded f′ adjunction to the source composite. Expand functoriality, then
replace the exchange adjunct by square transport followed by the f counit. Naturality of the
square comparison moves the f push comparison past it. The iterated mate/conjugation identity
identifies pullback of that push comparison followed by the E counit with the inverse pull
comparison followed by scalar extension of the integral counit. These substitutions give exactly
the displayed composite. -/
theorem integralConstructible_exchange_source_adjunct
    (sq : CommSq g' f' f g) (K : integralConstructible ℓ E X) :
    ((boundedConstructibleUpperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj E) ℓ k f').homEquiv _ _).symm
      (integralConstructibleSourceHom ℓ E k f g K ≫
        (boundedConstructibleBaseChange (Profinite.continuousMapRingObj E) ℓ k sq).app
          ((integralScalarConstructible ℓ E X).obj K)) =
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
