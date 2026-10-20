/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.OverSquare

public import Sheaf.Paper.ContinuousIntegralComparisons
import Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct
import Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct

/-! # Coherence of integral localization and the specified exchange map -/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]
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

/-- Integral coefficient extension respects the specified exchange arrow.
Source: Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-weil-pbc-continuous-integral-exchange-equality).
Proof. Apply injectivity of the inverse bounded f′ adjunction hom-equivalence. The source
and target adjunct calculations identify both sides with the same explicit composite. -/
theorem integralConstructible_exchange_equality
    (sq : CommSq g' f' f g) (K : integralConstructible ℓ E X) :
    integralConstructibleSourceHom ℓ E k f g K ≫
        (boundedConstructibleBaseChange (Profinite.continuousMapRingObj E) ℓ (sq.asOver (Spec (.of k)))).app
          ((integralScalarConstructible ℓ E X).obj K) =
      (integralScalarConstructible ℓ E Y').map
          ((boundedConstructibleBaseChange (integralCoeff ℓ E) ℓ (sq.asOver (Spec (.of k)))).app K) ≫
        integralConstructibleTargetHom ℓ E k f' g' K := by
  apply ((boundedConstructibleUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E) ℓ (f'.asOver (Spec (.of k)))).homEquiv _ _).symm.injective
  exact (integralConstructible_exchange_source_adjunct ℓ E k f g f' g' sq K).trans
    (integralConstructible_exchange_target_adjunct ℓ E k f g f' g' sq K).symm

end AlgebraicGeometry.ProEtale.CondensedRing
