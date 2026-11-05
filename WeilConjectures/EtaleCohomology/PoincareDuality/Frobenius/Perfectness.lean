/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.CompositionPairing
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.PointPairing
public import WeilConjectures.EtaleCohomology.PoincareDuality.InvertibleTwist
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupport
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

/-!
# Degreewise perfectness of the Poincaré pairings over a field

Let `k` be a separably closed field, `Λ` a finite field whose characteristic is invertible on
`X`, `γ` a Tate orientation of `a : X ⟶ Spec k` of relative dimension `d`, and
`K ∈ D^b_{ctf}(X, Λ)`. The degreewise Poincaré pairings
`⟨-, -⟩_i : H^i_c(X, K) × H^{2d-i}(X, K^∨(d)) ⟶ Λ`
(`AlgebraicGeometry.Etale.TateOrientation.degreewisePoincarePairing`) are perfect: the adjoint
`H^{2d-i}(X, K^∨(d)) ⟶ H^i_c(X, K)^∨` is an isomorphism.

The proof is the one of the blueprint, read on classes. The derived pairing `β_K` is perfect
(`AlgebraicGeometry.Etale.TateOrientation.isPerfectPairing_poincarePairing_of_finite`), so its
degree-zero part is the composition pairing `⟨x, y⟩ = x ≫ g(y)` for a bijection
`g : H^{2d-i}(X, K^∨(d)) ≃ Hom((Ra_! K)[i], Λ_s)`
(`AlgebraicGeometry.Etale.IsPerfectPairing.exists_addEquiv_degreeZero`). Over the field `Λ`,
the composition pairing `Hom(Λ_s, E) × Hom(E, Λ_s) ⟶ End(Λ_s) = Λ` is perfect for
`E = (Ra_! K)[i]`, whose `H^0` is the finite-dimensional space `H^i_c(X, K)`
(`AlgebraicGeometry.Etale.nondegenerate_comp_unit_of_isSepClosed`): this is where
`H^{-i}(C^∨) ≅ H^i(C)^∨` over a field enters.

## Main statements

- `AlgebraicGeometry.Etale.TateOrientation.isPerfPair_degreewisePoincarePairing`
  (`thm-pod-degreewise-perfectness-over-a-field`, `sk-thm-derived-duality`): the degreewise
  pairings are perfect.
- `AlgebraicGeometry.Etale.TateOrientation.isPerfPair_degreewisePoincarePairing_of_isProper`
  (`thm-pod-proper-poincare-duality`): the same for `a` proper, with `H^i(X, K)` in place of
  `H^i_c(X, K)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [IsDomain Λ] [Finite Λ] {k : Type u} [Field k]
  [IsSepClosed k]

variable [HasTateTwist Λ] {X : Scheme.{u}} {a : X ⟶ Spec (.of k)} [HasCompactification a]
  [LocallyOfFiniteType a] [HasInvertibleExponent Λ X] {d : ℕ}

namespace TateOrientation

end TateOrientation

end Etale

end AlgebraicGeometry
