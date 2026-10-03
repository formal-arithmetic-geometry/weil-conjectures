/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

/-!
# The arithmetic genus and the degree of a sheaf of modules

Let `X` be a scheme over a field `k`. We define its arithmetic genus `g = dim_k H^1(X, 𝒪_X)`
and the degree `deg ℒ = χ(ℒ) - χ(𝒪_X)` of a sheaf of modules on it, both in terms of the
cohomology of `WeilConjectures/AlgebraicGeometry/Cohomology/Defs.lean`.

There is no divisor-theoretic degree of a line bundle anywhere in Mathlib, and no group of
Cartier or Weil divisors on a scheme. The degree is therefore *defined* cohomologically, which
is the standard alternative definition (Stacks 0AYQ); on a proper curve it agrees with the
divisor-theoretic one.

## Main definitions

- `AlgebraicGeometry.Scheme.genus`: the genus `dim_k H^1(X, 𝒪_X)` of a curve.
- `AlgebraicGeometry.Scheme.Modules.degree`: the degree `χ(ℒ) - χ(𝒪_X)` of an invertible sheaf.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

section Defs

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The **genus** `g = dim_k H^1(X, 𝒪_X)` of a `k`-scheme `X`.

This is the arithmetic genus, and it is the genus in the usual sense when `X` is a smooth proper
geometrically integral curve over `k`; no hypotheses are imposed on `X` here, so for other `X`
the value carries no meaning. -/
noncomputable def genus : ℕ :=
  Modules.finrankH (X := X) k (SheafOfModules.unit X.ringCatSheaf) 1

end Defs

section Degree

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The **degree** `deg ℒ = χ(ℒ) - χ(𝒪_X)` of a sheaf of modules on a `k`-scheme `X`
(Stacks 0AYQ).

On a proper curve this agrees with the degree of the associated divisor class, and it is the
definition used throughout, because there is no divisor-theoretic degree of a line bundle in
Mathlib: neither Cartier nor Weil divisors on a scheme are defined there.

The formula is the degree in the usual sense only for sheaves of rank one; for a locally free
sheaf of rank `r` the degree is `χ(ℱ) - χ(𝒪_X^r)`. -/
noncomputable def Modules.degree (M : X.Modules) : ℤ :=
  M.eulerChar k - Modules.eulerChar (X := X) k (SheafOfModules.unit X.ringCatSheaf)

end Degree

end AlgebraicGeometry.Scheme
