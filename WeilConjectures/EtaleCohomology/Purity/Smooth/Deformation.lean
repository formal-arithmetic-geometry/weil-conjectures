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
Kummer-normalized comparison of `sk-prop-a1-inv` (ii). Its gluing half is now stated, as
`AlgebraicGeometry.Etale.exists_iso_leftDerivedUpperStar_of_locally`, but the normalized
comparison of `𝒞(g, s)` is not yet built from it.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_normalCone`
- `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_sectionNormalConeProj`
- `AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_deformation_affineSpace`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {V B : Scheme.{u}}

/-- Blueprint `sk-thm-dnc`: DNC invariance of the section dualizing line

Let `g : V ⟶ B` be smooth of pure relative dimension `d` with a closed section `s`, and let
`N_s ⟶ B` be its normal cone with zero section `0_N`. There is an isomorphism

`𝒞(g, s) ≅ 𝒞(π_N, 0_N)`

between the two section invariants which, in coordinates carrying `(g, s)` to
`(𝔸^d_B → B, 0)`, is the identity on the standard section invariant.

Here `N_s` is `AlgebraicGeometry.Scheme.Hom.sectionNormalCone`, the fibre over `t = 0` of the
deformation to the normal cone of `s`.

The proof runs the family object `ℱ = Ls̃^* ω_{g̃}` on the deformation space
`AlgebraicGeometry.Scheme.Hom.deformationSpace`: its fibres at `t = 1` and `t = 0`
are the two section invariants by base change, it is trivialized over `𝔾_{m,B}`, and weak
`𝔸¹`-invariance (`sk-prop-a1-inv`) identifies the two fibres. -/
-- TODO(unify): sk-thm-dnc — add the uniqueness and base-change clauses.
theorem nonempty_iso_sectionInvariant_normalCone (d : ℕ) (g : V ⟶ B)
    [SmoothOfRelativeDimension d g] [HasCompactification g] (s : B ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 B) [HasCompactification (Scheme.Hom.sectionNormalConeProj g s hs)]
    [HasInvertibleExponent Λ B] :
    Nonempty (sectionInvariant Λ g s ≅
      sectionInvariant Λ (Scheme.Hom.sectionNormalConeProj g s hs)
        (Scheme.Hom.sectionNormalConeZero g s hs)) :=
  sorry

/-- Blueprint `sk-lem-geometry`: Geometry of the deformation of a section

*The standard pair* (clause (4), cohomological half). For the zero section of
`𝔸^d_B ⟶ B`, the family object `ℱ = Ls̃^* ω_{g̃}` of the deformation is constant along `𝔸¹_B`:

`ℱ ≅ La^* Λ_B(d)[2d]`, with `a : 𝔸¹_B ⟶ B`.

The deformation space is `𝔸^d_{𝔸¹_B}` with `s̃` its zero section
(`AlgebraicGeometry.Scheme.Hom.exists_iso_deformationSpace_affineSpace`), so `ℱ` is the section
invariant of the standard pair over `𝔸¹_B`, which is `Λ(d)[2d]` by the `Rπ^!`-form of
`sk-prop-an` (ii) (`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_affineSpace`). This is
what `sk-thm-dnc` Step 2 uses on each étale chart. -/
theorem nonempty_iso_sectionInvariant_deformation_affineSpace (d : ℕ)
    [HasCompactification (Scheme.Hom.deformationProj (𝔸(ULift.{u} (Fin d); B) ↘ B)
      (AffineSpace.zeroSection (ULift.{u} (Fin d)) B)
      (AffineSpace.zeroSection_over (ULift.{u} (Fin d)) B))]
    [HasInvertibleExponent Λ B] :
    Nonempty (sectionInvariant Λ
        (Scheme.Hom.deformationProj (𝔸(ULift.{u} (Fin d); B) ↘ B)
          (AffineSpace.zeroSection (ULift.{u} (Fin d)) B)
          (AffineSpace.zeroSection_over (ULift.{u} (Fin d)) B))
        (Scheme.Hom.deformationSection (𝔸(ULift.{u} (Fin d); B) ↘ B)
          (AffineSpace.zeroSection (ULift.{u} (Fin d)) B)
          (AffineSpace.zeroSection_over (ULift.{u} (Fin d)) B)) ≅
      (L(((𝔸(ULift.{u} (Fin 1); B) ↘ B))^*[ModuleCat.{u + 1} Λ])).obj
        ((twistShift Λ B d).obj (constantComplex Λ B))) :=
  sorry

/-- Blueprint `sk-prop-an`: `𝔸¹ ⇒ 𝔸ⁿ`: the model purity

*Vector-bundle purity for the normal bundle of a section.* Let `g : V ⟶ B` be smooth of pure
relative dimension `d` with a closed section `s`, and let `π_N : N_s ⟶ B` be the normal bundle
of `s` (`AlgebraicGeometry.Scheme.Hom.sectionNormalCone`). Then

`ω_{π_N} = Rπ_N^! Λ_B ≅ Λ_{N_s}(d)[2d]`.

In the blueprint `N_s` is a vector bundle of rank `d` (`sk-lem-geometry` (1)) and this is the
vector-bundle form of `sk-prop-an` (ii) (`cor-pur-vector-bundle-purity`): the affine-space traces
of `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_affineSpace` on the trivializing
opens glue to a global trace, whose transpose is the isomorphism. It is stated for `N_s` only,
Mathlib having no vector bundles over a scheme.

Pulled back along the zero section `0_N` it gives `𝒞(π_N, 0_N) ≅ Λ_B(d)[2d]`, which is Step 3
of `sk-thm-smooth-purity`. It is not a consequence of smoothness of `π_N` alone: that would be
smooth purity for `π_N`, which is what is being proved. -/
theorem nonempty_iso_dualizingComplex_sectionNormalConeProj (d : ℕ) (g : V ⟶ B)
    [SmoothOfRelativeDimension d g] (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B)
    [HasCompactification (Scheme.Hom.sectionNormalConeProj g s hs)]
    [HasInvertibleExponent Λ B] :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) (Scheme.Hom.sectionNormalConeProj g s hs) ≅
      (twistShift Λ (Scheme.Hom.sectionNormalCone g s hs) d).obj
        (constantComplex Λ (Scheme.Hom.sectionNormalCone g s hs))) :=
  sorry

end Etale

end AlgebraicGeometry
