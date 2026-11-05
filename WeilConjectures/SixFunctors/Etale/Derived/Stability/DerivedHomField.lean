/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHom
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.VerdierDual
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHomGeneric
public import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleSurjectivePullback
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension

/-!
# The finite-coefficient internal Hom estimate over an arbitrary field

For a finite coefficient ring `Λ` whose exponent is invertible on a field `k`, and `X` of finite
type over `k` with `dim X ≤ d`, the internal hom of two bounded constructible complexes of Tor
amplitude `[a, b]` and `[c, e]` is bounded constructible of Tor amplitude
`[c - b - 2d, e - a + 2d]`
(`AlgebraicGeometry.Etale.boundedConstructible_and_torAmplitudeIn_derivedHom_of_field`).

Over an algebraically closed field this is `AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom`
and `AlgebraicGeometry.Etale.boundedConstructible_derivedHom`. In general we base change to an
algebraic closure `k̄` of `k`: the internal hom commutes with this base change
(`AlgebraicGeometry.Etale.isIso_derivedHomUpperStarComparison_of_generic`), the base change does
not increase the dimension, and bounded constructibility and Tor amplitude descend along the
surjective morphism `X_k̄ ⟶ X`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

end Etale

end AlgebraicGeometry
