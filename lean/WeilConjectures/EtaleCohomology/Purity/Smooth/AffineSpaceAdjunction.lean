/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.Affine
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass

/-!
# The affine-space ambient adjunction

For the projection `p_d : 𝔸^d_S ⟶ S` of relative affine space, the direct image with compact
support `Rp_{d!}` is left adjoint to the twisted pullback `p_d^*(d)[2d]` on the entire derived
categories of étale sheaves of `Λ`-modules (blueprint `cor-amb-affine-space-adjunction`, of the
subsection `sk-prop-sf-cbc`). Its proof composes the extension by zero along `𝔸¹_S ⊆ ℙ¹_S` with
the projective-line adjunction `Rq_* ⊣ q^*(1)[2]` (`thm-amb-p1-adjunction`), which is built from
the projective-line trace; neither is available yet, so the statement is recorded here with
`sorry`.

Since `Rp_d^!` is *defined* as the right adjoint of `Rp_{d!}`, the adjunction identifies
`Rp_d^!` with `p_d^*(d)[2d]`: this is how affine-line purity
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineLine`) is deduced.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

/-- Blueprint `cor-amb-affine-space-adjunction`: affine-space ambient adjunction.

For the projection `p_d : 𝔸^d_S ⟶ S` of relative affine space over a scheme `S` on which the
exponent of `Λ` is invertible, on the entire derived categories of étale sheaves of
`Λ`-modules,

`Rp_{d!} ⊣ p_d^*(d)[2d]`. -/
theorem nonempty_rightDerivedLowerShriek_adjunction_affineSpace [HasTateTwist.IsNormalized Λ]
    (d : ℕ) (S : Scheme.{u}) [HasInvertibleExponent Λ S] :
    Nonempty (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) (𝔸(ULift.{u} (Fin d); S) ↘ S) ⊣
      L(((𝔸(ULift.{u} (Fin d); S) ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
        twistShift Λ 𝔸(ULift.{u} (Fin d); S) d) :=
  sorry

end Etale

end AlgebraicGeometry
