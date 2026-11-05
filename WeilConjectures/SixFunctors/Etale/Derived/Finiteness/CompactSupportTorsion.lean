/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.SepClosedPoint

/-!
# Compactly supported cohomology of torsion complexes is perfect

The finite stage of `sk-prop-sf-trace-perfectness` for a complex of sheaves of modules over a
Noetherian ring `Λ` which is killed by an integer `N` invertible on the base. This is the form in
which the finite stages `A_{E,n} = 𝒪_E/𝔪_Eⁿ` occur at the integral stage `Λ = 𝒪_E`: an object of
`D(X_ét, A_{E,n})` is recorded through its restriction of scalars to `𝒪_E`, as in
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

end AlgebraicGeometry.Etale
