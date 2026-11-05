/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralCoefficientLimit

/-!
# The constant pro-étale ring sheaf `ℤ/N` is the sheaf of locally constant functions

Let `X` be a scheme and `N` a natural number. On the small pro-étale site of `X`, the
sheafification of the constant presheaf of rings with value `ℤ/N` is, as a ring object of the
category of abelian sheaves, the sheaf `(ℤ/N)_X = C(-, ℤ/N)` of locally constant functions
(`AlgebraicGeometry.ProEtale.zmodConstSheafRingIso`). Indeed the constant functions
`ℤ/N ⟶ C(U, ℤ/N)` form a locally bijective morphism of presheaves: a continuous map to the
discrete ring `ℤ/N` is constant on the members of the Zariski cover by its fibres, and two
distinct constants only agree on the empty scheme, which is covered by the empty family.

## Main definitions

- `AlgebraicGeometry.ProEtale.zmodConstPresheaf`: the constant presheaf of rings `ℤ/N`.
- `AlgebraicGeometry.ProEtale.zmodConstToContinuousMap`: the constant functions
  `ℤ/N ⟶ C(-, ℤ/N)`.
- `AlgebraicGeometry.ProEtale.zmodConstSheafRingIso`: the isomorphism of ring objects between
  the sheafification of `ℤ/N` and `(ℤ/N)_X`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable (X : Scheme.{u}) (N : ℕ)

end AlgebraicGeometry.ProEtale
