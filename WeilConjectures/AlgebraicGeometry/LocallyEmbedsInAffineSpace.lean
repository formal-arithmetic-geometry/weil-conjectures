/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpaceClosedChart

/-!
# Morphisms locally embedding into affine spaces of bounded dimension

A morphism `q : T ⟶ S` *locally embeds into `𝔸ᵐ_S`*
(`AlgebraicGeometry.Scheme.Hom.LocallyEmbedsInAffineSpace q m`) if every point of `T` has an open
neighbourhood `V` with an immersion `V ⟶ 𝔸ⁿ_S` over `S` into an affine space of dimension
`n ≤ m`. This is the dimension measure of the induction in Gabber's Künneth formula for nearby
cycles (blueprint `sk-prop-tf-nearby-external-kunneth`, "Finite support"): slicing along one
coordinate of such a chart lowers the dimension of the chart by one.

## Main statements

* `AlgebraicGeometry.Scheme.Hom.LocallyEmbedsInAffineSpace.restrict`: restriction to an open;
* `AlgebraicGeometry.Scheme.Hom.LocallyEmbedsInAffineSpace.of_isPullback`: stability under base
  change;
* `AlgebraicGeometry.Scheme.Hom.exists_locallyEmbedsInAffineSpace`: a quasi-compact morphism
  locally of finite type to an affine scheme locally embeds into some `𝔸ᵐ_S`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {T S : Scheme.{u}}

namespace LocallyEmbedsInAffineSpace

variable {q : T ⟶ S} {m : ℕ}

end LocallyEmbedsInAffineSpace

end Scheme.Hom

end AlgebraicGeometry
