/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Deformation to the normal cone of a section

For a smooth morphism `g : V ⟶ B` with a closed section `s : B ⟶ V`, the *deformation to the
normal cone of the section* is

`𝒟_s V = Bl_{s(B) × {0}} (V ×_B 𝔸¹_B) ∖ (strict transform of the closed fibre)`,

the blow-up of `V ×_B 𝔸¹_B` along `s(B) × {0}` with the strict transform of the fibre over
`t = 0` removed. It carries a morphism `g̃ : 𝒟_s V ⟶ 𝔸¹_B` with a section
`s̃ : 𝔸¹_B ⟶ 𝒟_s V`; the fibre of `(g̃, s̃)` over `t = 1` is `(g, s)` and the fibre over
`t = 0` is `(N_s → B, 0_N)`, so the deformation interpolates between a smooth morphism with a
section and a vector bundle with its zero section.

Equivalently `𝒟_s V = Spec_V (⨁_{r ∈ ℤ} I_s^r t^{-r})` is the extended Rees construction,
with `I_s^r = 𝒪_V` for `r ≤ 0`; inverting `t` gives `V × 𝔾_m` and setting `t = 0` gives the
normal cone.

## Implementation notes

The pinned Mathlib has no relative `Spec` of a quasi-coherent graded algebra and the project's
blow-up is not yet available along an arbitrary closed subscheme of a non-affine scheme, so
the deformation space and its two structure morphisms are packaged in a single `opaque`
constant. It depends genuinely on its arguments and introduces no `sorryAx`, but it satisfies
no equations; the blueprint content is the lemma below, not the construction.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.deformationToNormalCone`: the deformation space `𝒟_s V`.
- `AlgebraicGeometry.Scheme.Hom.deformationProj`: `g̃ : 𝒟_s V ⟶ 𝔸¹_B`.
- `AlgebraicGeometry.Scheme.Hom.deformationSection`: `s̃ : 𝔸¹_B ⟶ 𝒟_s V`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.deformationToNormalCone_spec`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {V B : Scheme.{u}}

namespace Scheme.Hom

/-- The deformation to the normal cone of a section, packaged with its two structure
morphisms: the scheme `𝒟_s V`, the morphism `g̃ : 𝒟_s V ⟶ 𝔸¹_B` and its section
`s̃ : 𝔸¹_B ⟶ 𝒟_s V`.

Mathlib has neither the relative `Spec` of the extended Rees algebra nor a blow-up along an
arbitrary closed subscheme, so this is an `opaque` placeholder; it satisfies no equations. The
three components are packaged together because the two morphisms have no type before the
scheme is known. -/
-- TODO(unify): sk-def-purity-conv
noncomputable opaque deformationData (g : V ⟶ B) (s : B ⟶ V) :
    Σ D : Scheme.{u}, (D ⟶ 𝔸(ULift.{u} (Fin 1); B)) × (𝔸(ULift.{u} (Fin 1); B) ⟶ D) :=
  ⟨𝔸(ULift.{u} (Fin 1); B), 𝟙 _, 𝟙 _⟩

/-- The deformation to the normal cone `𝒟_s V` of a closed section `s` of `g : V ⟶ B`. -/
noncomputable def deformationToNormalCone (g : V ⟶ B) (s : B ⟶ V) : Scheme.{u} :=
  (deformationData g s).1

/-- The structure morphism `g̃ : 𝒟_s V ⟶ 𝔸¹_B` of the deformation to the normal cone. -/
noncomputable def deformationProj (g : V ⟶ B) (s : B ⟶ V) :
    deformationToNormalCone g s ⟶ 𝔸(ULift.{u} (Fin 1); B) :=
  (deformationData g s).2.1

/-- The section `s̃ : 𝔸¹_B ⟶ 𝒟_s V` of the deformation to the normal cone. -/
noncomputable def deformationSection (g : V ⟶ B) (s : B ⟶ V) :
    𝔸(ULift.{u} (Fin 1); B) ⟶ deformationToNormalCone g s :=
  (deformationData g s).2.2

/-- Blueprint `sk-lem-geometry`: Geometry of the deformation of a section

Let `g : V ⟶ B` be smooth of pure relative dimension `d` with a closed section `s`, and let
`N_s ⟶ B` be the normal bundle of `s` with zero section `0_N`. Then:

1. `s̃` really is a section of `g̃`, and `g̃` is again smooth of pure relative dimension `d`:
   étale-locally there are relative coordinates `x₁, …, x_d` on `V` in which `s` is
   `x_i = 0`, and on the deformation chart `u_i = x_i / t` the deformation is
   `𝔸^d × 𝔸¹` over the base;
2. *the fibre over `t = 1`* is `(g, s)`: there is a morphism `ι₁ : V ⟶ 𝒟_s V` making the
   square with `g̃` and the unit section cartesian, and carrying `s` to `s̃`;
3. *the fibre over `t = 0`* is `(π_N, 0_N)`: likewise for the normal cone of `s` and the
   zero section of the affine line.

All of this commutes with base change in `B` and with étale localization. -/
theorem deformationToNormalCone_spec (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    deformationSection g s ≫ deformationProj g s = 𝟙 _ ∧
    SmoothOfRelativeDimension d (deformationProj g s) ∧
    (∃ ι : V ⟶ deformationToNormalCone g s,
      IsPullback ι g (deformationProj g s) (AffineSpace.oneSection (ULift.{u} (Fin 1)) B) ∧
        s ≫ ι = AffineSpace.oneSection (ULift.{u} (Fin 1)) B ≫ deformationSection g s) ∧
    (∃ ι : s.normalCone ⟶ deformationToNormalCone g s,
      IsPullback ι s.normalConeProj (deformationProj g s)
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B) ∧
        s.normalConeZero ≫ ι =
          AffineSpace.zeroSection (ULift.{u} (Fin 1)) B ≫ deformationSection g s) :=
  sorry

end Scheme.Hom

end AlgebraicGeometry
