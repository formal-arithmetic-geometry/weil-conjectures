/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.AlgebraicGeometry.VectorBundle

/-!
# The normal bundle of a section

Let `g : V ⟶ B` be a morphism with a section `s : B ⟶ V`. The conormal sheaf `I/I²` of the
immersion `s` is canonically `s^* Ω_{V/B}`: the conormal sequence
`I/I² ⟶ s^* Ω_{V/B} ⟶ Ω_{B/B} = 0` is exact, and it is split on the left by the derivation
`a ↦ a - g^* s^* a` of `𝒪_V` into `I/I²` ([Stacks, Tag 0474]). So the *normal bundle* of the
section is

`N_s = Spec_B (Sym_{𝒪_B} (I/I²)) = V(s^* Ω_{V/B})`,

the vector bundle (`AlgebraicGeometry.Scheme.Modules.vectorBundle`) of the module
`s^* Ω_{V/B}`. When `g` is smooth of pure relative dimension `d`, `Ω_{V/B}` is locally free of
rank `d` (`AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFreeOfRank_relativeDifferentials`), so
`N_s` is a vector bundle of rank `d` (blueprint `def-pur-normal-bundle`).

This is the normal cone datum (`AlgebraicGeometry.Scheme.Hom.NormalConeData`) that the
deformation to the normal cone of a section (`sk-lem-geometry`) is about: it is determined by
`g` and `s`, and not an arbitrary vector bundle with a zero section.

For the diagonal `Δ : X ⟶ X ×_Y X` of a smooth `f : X ⟶ Y`, a section of the first projection
`p₁`, the conormal sheaf is `Δ^* Ω_{X ×_Y X / X} = Δ^* p₂^* Ω_{X/Y} = Ω_{X/Y}`, so `N_Δ` is the
relative tangent bundle `T_{X/Y}` (`sk-lem-diag-reg`).

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.sectionConormal`: the conormal sheaf `s^* Ω_{V/B}` of a section.
- `AlgebraicGeometry.Scheme.Hom.sectionNormalCone`: the normal bundle `V(s^* Ω_{V/B})` of a
  section, as a normal cone datum.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.isVectorBundleOfRank_sectionNormalCone`: for `g` smooth of
  pure relative dimension `d`, the normal bundle is a vector bundle of rank `d`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

variable {V B : Scheme.{u}} (g : V ⟶ B) (s : B ⟶ V)

/-- The conormal sheaf `s^* Ω_{V/B}` of a section `s` of `g : V ⟶ B`; it is canonically the
conormal sheaf `I/I²` of the immersion `s` ([Stacks, Tag 0474]). -/
noncomputable def sectionConormal : B.Modules :=
  (Modules.pullback s).obj g.relativeDifferentials

/-- For `g` smooth of pure relative dimension `d`, the conormal sheaf of a section is locally free
of rank `d`. -/
instance isFiniteLocallyFreeOfRank_sectionConormal (d : ℕ) [SmoothOfRelativeDimension d g] :
    (g.sectionConormal s).IsFiniteLocallyFreeOfRank d :=
  have := g.isFiniteLocallyFreeOfRank_relativeDifferentials d
  inferInstanceAs (((Modules.pullback s).obj g.relativeDifferentials).IsFiniteLocallyFreeOfRank d)

/-- For `g` smooth of pure relative dimension `d`, the conormal sheaf of a section is
quasi-coherent. -/
lemma isQuasicoherent_sectionConormal (d : ℕ) [SmoothOfRelativeDimension d g] :
    (g.sectionConormal s).IsQuasicoherent :=
  Modules.isQuasicoherent_of_isLocallyFreeOfRank _ d

/-- Blueprint `def-pur-normal-bundle`: Normal bundle and zero section

The *normal bundle* `N_s = Spec_B (Sym (I/I²)) = V(s^* Ω_{V/B})` of a section `s` of a
morphism `g : V ⟶ B` smooth of pure relative dimension `d`, with its projection and zero section
(`AlgebraicGeometry.Scheme.Modules.vectorBundle` of `AlgebraicGeometry.Scheme.Hom.sectionConormal`),
as a normal cone datum of `s` of codimension `d`. -/
noncomputable def sectionNormalCone (d : ℕ) [SmoothOfRelativeDimension d g] :
    NormalConeData d s :=
  letI := g.isQuasicoherent_sectionConormal s d
  { scheme := (g.sectionConormal s).vectorBundle
    proj := (g.sectionConormal s).vectorBundleProj
    zeroSection := (g.sectionConormal s).vectorBundleZeroSection
    zeroSection_comp_proj := (g.sectionConormal s).vectorBundleZeroSection_vectorBundleProj
    isClosedImmersion_zeroSection := inferInstance
    smoothOfRelativeDimension_proj := inferInstance }

/-- For `g` smooth of pure relative dimension `d`, the normal bundle of a section is a vector
bundle of rank `d`. -/
instance isVectorBundleOfRank_sectionNormalCone (d : ℕ) [SmoothOfRelativeDimension d g] :
    IsVectorBundleOfRank d (g.sectionNormalCone s d).proj (g.sectionNormalCone s d).zeroSection :=
  letI := g.isQuasicoherent_sectionConormal s d
  inferInstanceAs (IsVectorBundleOfRank d (g.sectionConormal s).vectorBundleProj
    (g.sectionConormal s).vectorBundleZeroSection)

end AlgebraicGeometry.Scheme.Hom
