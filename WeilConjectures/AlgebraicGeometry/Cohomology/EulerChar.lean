/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

/-!
# The arithmetic genus and the cohomological degree of a sheaf of modules

Let `X` be a scheme over a field `k`. We define its arithmetic genus `dim_k H^1(X, 𝒪_X)` and the
degree `deg ℒ = χ(ℒ) - χ(𝒪_X)` of an invertible sheaf on it, both in terms of the cohomological
invariants `AlgebraicGeometry.Scheme.Modules.finrankH` and the Euler characteristic
`AlgebraicGeometry.Scheme.Modules.eulerChar`.

There is no divisor-theoretic degree of a line bundle anywhere in Mathlib, and no group of
Cartier or Weil divisors on a scheme. The degree is therefore *defined* cohomologically, which
is the standard alternative definition (Stacks 0AYQ); on a proper curve it agrees with the
divisor-theoretic one.

## Main definitions

- `AlgebraicGeometry.Scheme.arithmeticGenus`: the arithmetic genus `dim_k H^1(X, 𝒪_X)`.
- `AlgebraicGeometry.Scheme.Modules.degree`: the degree `χ(ℒ) - χ(𝒪_X)` of an invertible sheaf.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.degree_congr`: the degree only depends on the isomorphism
  class of the sheaf.
- `AlgebraicGeometry.Scheme.Modules.degree_unit`: the structure sheaf has degree `0`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

section Defs

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The **arithmetic genus** `dim_k H^1(X, 𝒪_X)` of a `k`-scheme `X`.

When `X` is a smooth proper geometrically integral curve over `k` this is the genus of `X`; no
hypotheses are imposed on `X` here, so for other `X` the value carries no meaning.

TODO: for a smooth proper geometrically integral curve `f : X ⟶ Spec k`, Serre duality
identifies this with `AlgebraicGeometry.Scheme.Hom.genus f = dim_k H^0(X, Ω¹_{X/k})`. -/
noncomputable def arithmeticGenus : ℕ :=
  Modules.finrankH (X := X) k (SheafOfModules.unit X.ringCatSheaf) 1

end Defs

section Degree

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The **degree** `deg ℒ = χ(ℒ) - χ(𝒪_X)` of a sheaf of modules `ℒ` on a `k`-scheme `X`
(Stacks 0AYQ).

The value is the degree in the usual sense only for an invertible `ℒ` on a proper curve, where
it agrees with the degree of the associated divisor class; for other sheaves it is just a
difference of Euler characteristics. -/
noncomputable def Modules.degree (M : X.Modules) : ℤ :=
  M.eulerChar k - Modules.eulerChar (X := X) k (SheafOfModules.unit X.ringCatSheaf)

/-- The degree only depends on the isomorphism class of a sheaf of modules. -/
lemma Modules.degree_congr {M N : X.Modules} (e : M ≅ N) : M.degree k = N.degree k := by
  rw [degree, degree, eulerChar_congr k e]

@[simp]
lemma Modules.degree_unit :
    Modules.degree (X := X) k (SheafOfModules.unit X.ringCatSheaf) = 0 :=
  sub_self _

end Degree

end AlgebraicGeometry.Scheme
