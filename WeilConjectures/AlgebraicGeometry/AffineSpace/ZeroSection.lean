/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The zero section of affine space as a zero locus

The zero section `0 : S ⟶ 𝔸(n; S)` identifies `S` with the closed subscheme `V(t_i)` of
`𝔸(n; S)` cut out by the coordinates: the coordinates vanish along the zero section, so it
factors through `V(t_i)`, and the composite `V(t_i) ⟶ 𝔸(n; S) ⟶ S` is inverse to the
factorisation since a morphism to `𝔸(n; S)` is determined by its composite with the projection
and the pullbacks of the coordinates.

## Main definitions

- `AlgebraicGeometry.AffineSpace.zeroSectionIsoZeroLocusSubscheme`: `S ≅ V(t_i)`, compatibly
  with the zero section and the inclusion of `V(t_i)`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.AffineSpace

variable (n : Type u) (S : Scheme.{u})

/-- The zero section identifies `S` with the closed subscheme of `𝔸(n; S)` cut out by the
coordinates. The set `s` of sections is an argument with `Set.range (coord S) = s`, so that the
isomorphism applies to any presentation of that set, for instance `{coord S i}` when `n` has a
single element. -/
noncomputable def zeroSectionIsoZeroLocusSubscheme {s : Set Γ(𝔸(n; S), ⊤)}
    (hs : Set.range (coord S) = s) : S ≅ 𝔸(n; S).zeroLocusSubscheme s where
  hom := (zeroSection n S).liftZeroLocusSubscheme (by
    rintro _ ht
    obtain ⟨i, rfl⟩ := hs ▸ ht
    exact zeroSection_appTop_coord n S i)
  inv := 𝔸(n; S).zeroLocusSubschemeι s ≫ 𝔸(n; S) ↘ S
  hom_inv_id := by simp
  inv_hom_id := by
    rw [← cancel_mono (𝔸(n; S).zeroLocusSubschemeι s)]
    simp only [Category.assoc, Scheme.Hom.liftZeroLocusSubscheme_zeroLocusSubschemeι,
      Category.id_comp]
    refine AffineSpace.hom_ext (by simp) (fun i ↦ ?_)
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, zeroSection_appTop_coord,
      map_zero]
    exact (Scheme.zeroLocusSubschemeι_appTop (hs ▸ ⟨i, rfl⟩)).symm

@[reassoc (attr := simp)]
lemma zeroSectionIsoZeroLocusSubscheme_hom_zeroLocusSubschemeι {s : Set Γ(𝔸(n; S), ⊤)}
    (hs : Set.range (coord S) = s) :
    (zeroSectionIsoZeroLocusSubscheme n S hs).hom ≫ 𝔸(n; S).zeroLocusSubschemeι s =
      zeroSection n S := by
  simp [zeroSectionIsoZeroLocusSubscheme]

end AlgebraicGeometry.AffineSpace
