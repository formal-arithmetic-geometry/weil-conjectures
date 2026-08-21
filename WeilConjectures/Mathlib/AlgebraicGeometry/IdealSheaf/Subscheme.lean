/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions

/-!
# Complements on the subscheme cut out by an ideal sheaf

This file adds two independent complements to `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.

## Base change of the subscheme cut out by an ideal sheaf

The affine cover of the closed subscheme `V(I)` cut out by a quasi-coherent ideal `I` is
obtained by base change: over an affine open `U` of `X`, the square formed by the chart
`Spec (Γ(X, U) ⧸ I(U)) ⟶ V(I)` of `I.subschemeCover`, the closed immersion `I.subschemeι`
and `U.2.fromSpec` is a pullback
(`AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subschemeCover_map`).

Pasting this square with `Spec` of the pushout square `CommRingCat.isPushout_quotient`
computes the base change of `I.subschemeι` along an arbitrary affine probe
`Spec.map φ ≫ U.2.fromSpec`: it is the closed immersion cut out by the extended ideal
`I(U)·S` (`AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subschemeι_specMap_fromSpec`).

## The map to the scheme-theoretic image is scheme-theoretically dominant

For a quasi-compact `f : X ⟶ Y`, Mathlib factors `f` as `f.toImage ≫ f.imageι` through the
scheme-theoretic image, and knows that `f.toImage` is dominant and quasi-compact. It does not
record that `f.toImage` is *scheme-theoretically* dominant, which is the stronger statement
that makes the image the smallest closed subscheme through which `f` factors. This file adds
it, in the form `AlgebraicGeometry.Scheme.Hom.ker_toImage : f.toImage.ker = ⊥`.

The proof is the expected one and uses no new input: `f.toImage.app` is injective over the
preimage of an affine open of `Y` (`AlgebraicGeometry.Scheme.Hom.toImage_app_injective`), those
preimages are affine because `f.imageι` is a closed immersion, and they cover the image, so
the kernel ideal vanishes on a cover by affine opens.

## Main results

- `AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subschemeCover_map`
- `AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subschemeι_specMap_fromSpec`
- `AlgebraicGeometry.Scheme.Hom.ker_toImage`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)

/-- The affine chart of the subscheme over an affine open is the fibre product: the
square with the chart `Spec (Γ(X, U) ⧸ I(U)) ⟶ V(I)` and `fromSpec` is a pullback. -/
lemma isPullback_subschemeCover_map :
    IsPullback (I.subschemeCover.f U)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))))
      I.subschemeι U.2.fromSpec := by
  refine (IsOpenImmersion.isPullback _ _ _ _ ?_ ?_).flip
  · exact (I.subschemeCover_map_subschemeι U).trans (I.glueDataObjι_ι U)
  · rw [U.2.opensRange_fromSpec, opensRange_subschemeCover_map]

/-- **The subscheme of an ideal sheaf base changes to the subscheme of the extended
ideal.** Along a morphism `Spec S ⟶ X` of the form `Spec.map φ ≫ U.2.fromSpec` with `U` an
affine open, the base change of `I.subschemeι` is `Spec` of the quotient of `S` by the
extension of `I(U)` along `φ`. -/
lemma isPullback_subschemeι_specMap_fromSpec {S : CommRingCat.{u}} (φ : Γ(X, U.1) ⟶ S) :
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((I.ideal U).map φ.hom) φ.hom
        Ideal.le_comap_map)) ≫ I.subschemeCover.f U)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((I.ideal U).map φ.hom))))
      I.subschemeι (Spec.map φ ≫ U.2.fromSpec) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_quotient φ (I.ideal U))).paste_horiz
      (I.isPullback_subschemeCover_map U)

/-- The inclusions of the subschemes attached to equal ideal sheaves agree up to
`eqToHom`. -/
lemma subschemeι_eqToHom {I J : X.IdealSheafData} (e : I = J) :
    eqToHom (congrArg subscheme e) ≫ J.subschemeι = I.subschemeι := by
  subst e
  simp

end AlgebraicGeometry.Scheme.IdealSheafData

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
