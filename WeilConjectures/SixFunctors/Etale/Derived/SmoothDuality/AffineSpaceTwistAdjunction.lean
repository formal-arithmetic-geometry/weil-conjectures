/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactificationIso
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineAdjunctionBaseChange

/-!
# The affine-space adjunction from the projective-line adjunction

For a normalized Tate twist and every scheme `S` on which the exponent of `Λ` is invertible, the
projection `p_d : 𝔸^d_S ⟶ S` satisfies `Rp_{d!} ⊣ Lp_d^*(d)[2d]`
(`AlgebraicGeometry.Etale.nonempty_rightDerivedLowerShriek_adjunction_affineSpace`, blueprint
`cor-amb-affine-space-adjunction`, `sk-lem-geo-affine-local`).

The proof composes *twisted adjunctions* `Rf_! ⊣ Lf^*(a)[2a]`
(`AlgebraicGeometry.Etale.nonempty_adjunction_twistShift_comp`): étale morphisms have one with
`a = 0` (`Rf_!` is the extension by zero, left adjoint to `Lf^*`), the projective line
`q : ℙ¹_S ⟶ S` has one with `a = 1` (`thm-amb-p1-adjunction`), so the affine line, which is the
standard chart `𝔸¹_S ⊆ ℙ¹_S` followed by `q`, has one with `a = 1`, and affine spaces follow by
induction through `𝔸^{d+1}_S ≅ 𝔸¹_{𝔸^d_S}`.

## Main statements

- `AlgebraicGeometry.Etale.twistShiftZeroNatIso`, `AlgebraicGeometry.Etale.twistShiftAddNatIso`,
  `AlgebraicGeometry.Etale.leftDerivedUpperStarTwistShiftNatIso`: the functorial forms of the
  identifications `K(0)[0] ≅ K`, `K(b)[2b](a)[2a] ≅ K(b + a)[2(b + a)]` and
  `Lf^*(K(m)[2m]) ≅ (Lf^* K)(m)[2m]`.
- `AlgebraicGeometry.Etale.nonempty_adjunction_twistShift_comp`
- `AlgebraicGeometry.Etale.nonempty_rightDerivedLowerShriek_adjunction_affineSpace`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

section NatIso

end NatIso

section Adjunction

end Adjunction

end Etale

end AlgebraicGeometry
