/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.MittagLeffler

/-!
# Uniform Mittag-Leffler property for towers of finite locally constant sheaves

Let `X` be a scheme with noetherian underlying space and `(Hₙ)ₙ` a tower of finite locally
constant étale sheaves with finite stalks. Suppose that at every point `x` the tower of stalks is
uniformly Mittag-Leffler: there is `c₀ x` such that for every `m` the images of
`(H_{m+j})_x ⟶ (H_m)_x` are the same for all `j ≥ c₀ x`. Then the tower is uniformly
Mittag-Leffler with a constant independent of `x`: there is `c` such that for every `m` the image
of `H_{m+c} ⟶ H_m` is contained in the image of `H_k ⟶ H_m` for all `k ≥ m + c`
(`AlgebraicGeometry.Etale.exists_imageSubobject_le_of_forall_range_sheafFiber_eq`).

Indeed, the stalk cardinalities of the image subsheaves are locally constant, hence determined by
their values at finitely many points (one in each irreducible component), and an inclusion of
subsheaves with equal stalk cardinalities is an equality.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

end AlgebraicGeometry.Etale
