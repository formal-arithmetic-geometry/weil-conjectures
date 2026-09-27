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
its normal bundle with the zero section. Together with the model purity for `𝔸ⁿ` this is what
computes `ω_f` in the smooth case.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_normalCone`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {V B : Scheme.{u}}

/-- Blueprint `sk-thm-dnc`: DNC invariance of the section dualizing line

Let `g : V ⟶ B` be smooth of pure relative dimension `d` with a closed section `s`, and let
`N_s ⟶ B` be its normal bundle with zero section `0_N`. There is a unique isomorphism

`𝒞(g, s) ≅ 𝒞(π_N, 0_N)`

between the two section invariants which, in coordinates carrying `(g, s)` to
`(𝔸^d_B → B, 0)`, is the identity on the standard section invariant; it is compatible with
étale localization and with arbitrary base change in `B`.

The proof runs the family object `ℱ = Ls̃^* ω_{g̃}` on the deformation space of
`AlgebraicGeometry.Scheme.Hom.deformationToNormalCone`: its fibres at `t = 1` and `t = 0` are
the two section invariants by base change, it is trivialized over `𝔾_{m,B}`, and weak
`𝔸¹`-invariance (`sk-prop-a1-inv`) identifies the two fibres. Uniqueness is the uniqueness
clause of `𝔸¹`-invariance, normalization being taken at `t = 1`. -/
theorem nonempty_iso_sectionInvariant_normalCone (d : ℕ) (g : V ⟶ B)
    [SmoothOfRelativeDimension d g] [HasCompactification g] (s : B ⟶ V) [IsClosedImmersion s]
    [HasCompactification (Scheme.Hom.normalConeProj s)] (_hs : s ≫ g = 𝟙 B) :
    Nonempty (sectionInvariant Λ g s ≅
      sectionInvariant Λ (Scheme.Hom.normalConeProj s) (Scheme.Hom.normalConeZero s)) :=
  sorry

end Etale

end AlgebraicGeometry
