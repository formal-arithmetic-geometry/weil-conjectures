/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# The map to the scheme-theoretic image is scheme-theoretically dominant

For a quasi-compact `f : X ⟶ Y`, Mathlib factors `f` as `f.toImage ≫ f.imageι` through the
scheme-theoretic image, and knows that `f.toImage` is dominant and quasi-compact. It does not
record that `f.toImage` is *scheme-theoretically* dominant, which is the stronger statement
that makes the image the smallest closed subscheme through which `f` factors. This file adds
it, in the form `AlgebraicGeometry.Scheme.Hom.ker_toImage : f.toImage.ker = ⊥`.

The proof is the expected one and uses no new input: `f.toImage.app` is injective over the
preimage of an affine open of `Y` (`AlgebraicGeometry.Scheme.Hom.toImage_app_injective`), those
preimages are affine because `f.imageι` is a closed immersion, and they cover the image, so
the kernel ideal vanishes on a cover by affine opens.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The kernel of the map to the scheme-theoretic image is trivial: no closed subscheme of
`f.image` strictly smaller than `f.image` contains the image of `f`. -/
lemma ker_toImage [QuasiCompact f] : f.toImage.ker = ⊥ := by
  refine IdealSheafData.ext_of_iSup_eq_top
    (fun V : Y.affineOpens ↦ ⟨f.imageι ⁻¹ᵁ V.1, V.2.preimage f.imageι⟩) ?_ fun V ↦ ?_
  · rw [← preimage_iSup, iSup_affineOpens_eq_top, preimage_top]
  · rw [ker_apply]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (f.toImage_app_injective V)

instance [QuasiCompact f] : IsSchemeTheoreticallyDominant f.toImage := ⟨f.ker_toImage⟩

end AlgebraicGeometry.Scheme.Hom
