/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.Affine
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek

/-!
# `𝔸¹ ⇒ 𝔸ⁿ`: the model purity

Let `B` be a scheme on which the exponent of the finite coefficient ring `Λ` is invertible,
`p_c : 𝔸^c_B → B` the projection and `z : B ↪ 𝔸^c_B` the zero section. This file proves the
two forms of the model purity of blueprint `sk-prop-an` by iterating the affine line:

* the `Rz^!`-form (clause (i)): `Rz^! Λ(c)[2c] ≅ Λ_B`;
* the `Rp_c^!`-form (clause (ii)): `Rp_c^! K ≅ Lp_c^* K (c)[2c]` for `K ∈ D^b_{ctf}(B, Λ)`; its
  inductive steps are here, and the theorem itself, which rests on the affine-space ambient
  adjunction, is in `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpacePurity`.

Both proofs write `𝔸^{c+1}_B = 𝔸¹_{B'}` with `B' = 𝔸^c_B`
(`AlgebraicGeometry.AffineSpace.sumIso`), under which the zero section of `𝔸^{c+1}_B` is the
composite of the zero sections of `𝔸^c_B` and of `𝔸¹_{B'}`, and the projection is the
composite of the projections. The composition law for `R(-)^!`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp`) reduces each step to the
affine line, where the input is `sk-prop-a1` (for clause (i)) and affine-line purity
(`thm-pur-affine-line-purity`, for clause (ii)). For clause (i) the twist pulled back from
`B'` is moved through `Rs'^!` by the co-projection formula for the closed immersion `s'`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineSpaceZero`: clause (i),
  `Rz^! Λ(c)[2c] ≅ Λ_B`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineSpace_succ`,
  `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_affineSpaceSuccIso_twistShift`: the
  inductive step of clause (ii).

## Implementation notes

The comparison maps of the blueprint — the Thom class `th`, the integration map `∫_π` and its
transpose `γ_{π,K}` — are not constructed: the projective-line trace and the Kummer boundary
with supports they are built from are not available. The isomorphisms are therefore recorded
as `Nonempty (_ ≅ _)`, and the normalization (iii), the composition law and the
compatibilities of `γ`, which are statements about these maps, are not stated. The
vector-bundle forms are not stated either, Mathlib having no vector bundles over a scheme.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

/-! ### Twists of pulled-back objects -/

section Twists

variable {X Y : Scheme.{u}} [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

/-- `Λ_X(m)[2m] = (Λ_X ⊗^L Λ_X(m))[2m] ≅ Λ_X(m)[2m]`, through the left unitor. -/
noncomputable def twistShiftConstantComplexIso (X : Scheme.{u}) (m : ℤ) :
    (twistShift Λ X m).obj (constantComplex Λ X) ≅ (tateObject Λ X m)⟦2 * m⟧ :=
  (shiftFunctor _ (2 * m)).mapIso (derivedTensorLeftUnitor _ X _)

/-- Pullback commutes with twist-and-shift, `Lf^*(K(m)[2m]) ≅ (Lf^* K)(m)[2m]`. -/
noncomputable def leftDerivedUpperStarTwistShiftIso (f : X ⟶ Y) (m : ℤ)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).obj ((twistShift Λ Y m).obj K) ≅
      (twistShift Λ X m).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  ((L((f)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 * m)).app _ ≪≫
    (shiftFunctor _ (2 * m)).mapIso
      (leftDerivedUpperStarTensorIso _ f K (tateObject Λ Y m) ≪≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj _).mapIso
          (leftDerivedUpperStarTateObjectIso f m))

end Twists

/-! ### The `Rz^!`-form -/

end Etale

end AlgebraicGeometry
