/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions

/-!
# DNC invariance of the section dualizing line

The deformation to the normal cone of a *section* transports the section invariant
`𝒞(g, s) = Ls^* ω_g` of a smooth morphism with a closed section to the section invariant of
its normal cone with the zero section. Together with the model purity for `𝔸ⁿ` this is what
computes `ω_f` in the smooth case.

## Implementation notes

The blueprint asserts that the isomorphism is *unique* once normalized at `t = 1`, and that it
is compatible with étale localization and with base change. Uniqueness is the uniqueness
clause of `𝔸¹`-invariance; it cannot be stated here, because the normalization refers to the
Kummer-normalized comparison of `sk-prop-a1-inv` (ii), whose gluing half is itself a TODO of
`WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_normalCone`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {V B : Scheme.{u}}

/-- Blueprint `sk-thm-dnc`: DNC invariance of the section dualizing line

Let `g : V ⟶ B` be smooth of pure relative dimension `d` with a closed section `s`, and let
`N_s ⟶ B` be its normal cone with zero section `0_N`. There is an isomorphism

`𝒞(g, s) ≅ 𝒞(π_N, 0_N)`

between the two section invariants which, in coordinates carrying `(g, s)` to
`(𝔸^d_B → B, 0)`, is the identity on the standard section invariant.

The proof runs the family object `ℱ = Ls̃^* ω_{g̃}` on the deformation space of
`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData`: its fibres at `t = 1` and `t = 0`
are the two section invariants by base change, it is trivialized over `𝔾_{m,B}`, and weak
`𝔸¹`-invariance (`sk-prop-a1-inv`) identifies the two fibres. -/
-- TODO(unify): sk-thm-dnc — add the uniqueness and base-change clauses.
theorem nonempty_iso_sectionInvariant_normalCone (d : ℕ) (g : V ⟶ B)
    [SmoothOfRelativeDimension d g] [HasCompactification g] (s : B ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 B) (N : Scheme.Hom.NormalConeData d s)
    [HasCompactification N.proj] [HasInvertibleExponent Λ B] :
    Nonempty (sectionInvariant Λ g s ≅ sectionInvariant Λ N.proj N.zeroSection) :=
  sorry

end Etale

end AlgebraicGeometry
