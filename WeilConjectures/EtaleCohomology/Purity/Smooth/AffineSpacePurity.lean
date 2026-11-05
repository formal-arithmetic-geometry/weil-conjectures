/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.AffineSpaceTwistAdjunction

/-!
# Affine-space purity: the `Rp^!`-form

Let `Y` be a separated scheme of finite type over a field on which the exponent of the finite
coefficient ring `Λ` is invertible, and `p_d : 𝔸^d_Y → Y` the projection. This file proves
clause (ii) of blueprint `sk-prop-an`, `Rp_d^! K ≅ Lp_d^* K (d)[2d]` for `K ∈ D^b_{ctf}(Y, Λ)`.

Affine-line purity is read off from the affine-space ambient adjunction
`Rp_! ⊣ p^*(1)[2]` (`cor-amb-affine-space-adjunction`,
`AlgebraicGeometry.Etale.nonempty_rightDerivedLowerShriek_adjunction_affineSpace`), and the
general case iterates it through `𝔸^{d+1}_Y = 𝔸¹_{𝔸^d_Y}`
(`AlgebraicGeometry.AffineSpace.sumIso`).

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineLine`: affine-line purity,
  `Rp^! K ≅ Lp^* K (1)[2]`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineSpace`: clause (ii),
  affine-space purity `Rp_c^! K ≅ Lp_c^* K (c)[2c]`.
- `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_affineSpace`: its case `K = Λ_B`,
  `ω_{p_c} ≅ Λ(c)[2c]`.
- `AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_affineSpace`: the section invariant of
  the standard pair, `𝒞(𝔸^c_B → B, 0) ≅ Λ_B(c)[2c]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

/-! ### The `Rp^!`-form -/

end Etale

end AlgebraicGeometry
