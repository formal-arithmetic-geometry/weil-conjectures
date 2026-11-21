/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedQbarComparisons
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedQbarExchangeLeftAdjunct
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedQbarExchangeRightAdjunct

/-! # The exchange equality for condensed finite-to-Qbar coefficient change -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))

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

/-- Coefficient extension respects the specified unit-square-counit exchange arrow. -/
theorem constructibleToQbar_exchange_equality
    (sq : CommSq g' f' f g) (K : PadicSubfieldConstructible X ℓ E) :
    constructibleToQbarSourceHom ℓ k E f g K ≫
        (boundedConstructibleBaseChange ℓ (sq.asOver (Spec (.of k)))).app
          ((constructibleToPadicAlgCl X ℓ E).obj K) =
      (constructibleToPadicAlgCl Y' ℓ E).map
          ((ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E
            (sq.asOver (Spec (.of k)))).app K) ≫
        constructibleToQbarTargetHom ℓ k E f' g' K := by
  apply ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
    (f'.asOver (Spec (.of k)))).homEquiv _ _).symm.injective
  exact (constructibleToQbar_exchange_left_adjunct ℓ k E f g f' g' sq K).trans
    (constructibleToQbar_exchange_right_adjunct ℓ k E f g f' g' sq K).symm

end AlgebraicGeometry.ProEtale.CondensedRing
