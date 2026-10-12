/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage

/-!
# Compact direct images: bounded constructibility and base change

For a separated finite-type morphism `f : X ⟶ S` between finite-type schemes over a field and a
finite coefficient ring `Λ` whose exponent is invertible on `S`, the compactly supported direct
image `Rf_!` preserves bounded constructibility, and its formation commutes with every base
change from a noetherian scheme. This is the input on compact supports used by Deligne's generic
constructibility theorem (`thm-fin-deligne-generic-open`).

## Main statements

- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek_and_isIso`
  (`lem-fin-compact-bounded-and-base-change`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `lem-fin-compact-bounded-and-base-change`: Compact direct images needed by the
generic argument.

Let `f : X ⟶ S` be a separated finite-type morphism (here: one admitting a compactification)
between finite-type schemes over a field `k`, and let `Λ` be a finite ring whose exponent is
invertible in `k`. For `K ∈ Dᵇc(X, Λ)`, the compact direct image `Rf_! K` is bounded
constructible, and for every morphism `v : S' ⟶ S` from a noetherian scheme, with base change
`f' : X' ⟶ S'`, the exchange `v^* Rf_! K ⟶ Rf'_! v_X^* K` is an isomorphism. -/
theorem boundedConstructible_rightDerivedLowerShriek_and_isIso {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))] {X S : Scheme.{u}} (f : X ⟶ S)
    [HasCompactification f] (aX : X ⟶ Spec (.of k)) (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aS] [QuasiCompact aS]
    (hf : f ≫ aS = aX)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) S
        ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) ∧
      ∀ (S' X' : Scheme.{u}) [IsNoetherian S'] (v : S' ⟶ S) (vX : X' ⟶ X) (f' : X' ⟶ S')
        [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback vX f' f v),
        IsIso ((rightDerivedLowerShriekBaseChangeMap Λ sq).app K) :=
  sorry

end Etale

end AlgebraicGeometry
