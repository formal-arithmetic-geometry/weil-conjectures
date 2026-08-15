/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Flat base change for scheme-theoretic images

We show that the factor map `g.toImage : T ⟶ g.image` through the scheme-theoretic
image of a quasi-compact morphism `g : T ⟶ Y` is scheme-theoretically dominant, and
deduce that formation of scheme-theoretic images commutes with flat base change
(blueprint: `lemma:nagata-scheme-image-flat-base-change`; Stacks Project Tag 081I):

- `AlgebraicGeometry.isSchemeTheoreticallyDominant_iff_isIso_imageι`: a morphism is
  scheme-theoretically dominant if and only if the inclusion of its scheme-theoretic
  image is an isomorphism;
- `AlgebraicGeometry.isSchemeTheoreticallyDominant_toImage`: the factor map through the
  scheme-theoretic image of a quasi-compact morphism is scheme-theoretically dominant;
- `AlgebraicGeometry.Scheme.Hom.ker_pullback_snd` and
  `AlgebraicGeometry.Scheme.Hom.ker_of_isPullback`: for `q : Y' ⟶ Y` flat, the kernel of
  the base change `T ×_Y Y' ⟶ Y'` is the pullback of the kernel of `g`;
- `AlgebraicGeometry.Scheme.Hom.image.pullbackIso`: the scheme-theoretic image of the
  base change is canonically isomorphic to the pullback of the scheme-theoretic image,
  compatibly with the closed immersions into `Y'`
  (`AlgebraicGeometry.Scheme.Hom.image.pullbackIso_hom_fst`) and with the factor maps
  (`AlgebraicGeometry.Scheme.Hom.image.toImage_pullbackIso_hom_snd`);
  `AlgebraicGeometry.Scheme.Hom.image.isPullback_imageι` is the same statement in the
  form of a cartesian square;
- `AlgebraicGeometry.Scheme.Hom.ker_morphismRestrict`: the special case of the
  restriction to an open subscheme of the target
  (blueprint: `lemma:nagata-scheme-image-restrict-open`).

The proof factors the base-changed morphism through the pullback of the
scheme-theoretic image: the comparison map is the flat base change of the
scheme-theoretically dominant factor map `Scheme.Hom.toImage`, and Mathlib's
`AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isPullback` (which encapsulates the
affine computation of the kernel of a flat base change) shows it has trivial kernel.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {T Y : Scheme.{u}}

/-- A morphism is scheme-theoretically dominant if and only if the closed immersion of
its scheme-theoretic image into the target is an isomorphism. -/
theorem isSchemeTheoreticallyDominant_iff_isIso_imageι (g : T ⟶ Y) :
    IsSchemeTheoreticallyDominant g ↔ IsIso g.imageι :=
  (isSchemeTheoreticallyDominant_iff g).trans
    (Scheme.isIso_subschemeι_iff_eq_bot g.ker).symm

variable (g : T ⟶ Y) [QuasiCompact g]

/-- The factor map `g.toImage : T ⟶ g.image` through the scheme-theoretic image of a
quasi-compact morphism is scheme-theoretically dominant: its kernel ideal sheaf
vanishes. This is checked on the affine cover of the image obtained by pulling back the
affine opens of `Y` along the closed immersion `g.imageι`, where the section map is
injective by `Scheme.Hom.toImage_app_injective`. -/
instance isSchemeTheoreticallyDominant_toImage :
    IsSchemeTheoreticallyDominant g.toImage := by
  refine ⟨Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens ↦ ⟨g.imageι ⁻¹ᵁ U.1, U.2.preimage g.imageι⟩)
    (g.imageι.iSup_preimage_eq_top (iSup_affineOpens_eq_top Y)) fun U ↦ ?_⟩
  simp only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (g.toImage_app_injective U)

/-- Flat base change for scheme-theoretic images, in kernel ideal sheaf form: for a
quasi-compact morphism `g : T ⟶ Y` and a flat morphism `q : Y' ⟶ Y`, the kernel of the
base change `T ×_Y Y' ⟶ Y'` is the pullback of the kernel of `g`.
(blueprint: `lemma:nagata-scheme-image-flat-base-change`; Stacks Project Tag 081I. The
blueprint and the Stacks Project assume `g` quasi-separated as well, but Mathlib's
kernel ideal sheaf theory only needs quasi-compactness.)

The proof factors the base change `T ×_Y Y' ⟶ Y'` through `g.image ×_Y Y'`: the first
factor is the flat base change of the scheme-theoretically dominant map `g.toImage`,
hence is itself scheme-theoretically dominant
(`AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isPullback`), so the kernel is
that of the closed immersion `g.image ×_Y Y' ⟶ Y'`, which is `g.ker.comap q` by
definition of the pullback of ideal sheaves. -/
theorem Scheme.Hom.ker_pullback_snd {Y' : Scheme.{u}} (q : Y' ⟶ Y) [Flat q] :
    (pullback.snd g q).ker = g.ker.comap q := by
  have w : pullback.snd g q ≫ q = (pullback.fst g q ≫ g.toImage) ≫ g.imageι := by
    rw [Category.assoc, g.toImage_imageι, pullback.condition]
  -- The comparison map `T ×_Y Y' ⟶ g.image ×_Y Y'` is the base change of `g.toImage`
  -- along the flat projection `g.image ×_Y Y' ⟶ g.image`.
  have hsq : IsPullback (pullback.lift (pullback.snd g q) (pullback.fst g q ≫ g.toImage) w)
      (pullback.fst g q) (pullback.snd q g.imageι) g.toImage := by
    refine .of_right ?_ (pullback.lift_snd _ _ _) (.of_hasPullback q g.imageι)
    rw [pullback.lift_fst, g.toImage_imageι]
    exact (IsPullback.of_hasPullback g q).flip
  haveI : IsSchemeTheoreticallyDominant
      (pullback.lift (pullback.snd g q) (pullback.fst g q ≫ g.toImage) w) :=
    .of_isPullback hsq.flip
  rw [← pullback.lift_fst (pullback.snd g q) (pullback.fst g q ≫ g.toImage) w,
    Scheme.Hom.ker_comp,
    Scheme.Hom.ker_eq_bot (pullback.lift (pullback.snd g q) (pullback.fst g q ≫ g.toImage) w),
    Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    Scheme.IdealSheafData.ker_subschemeι]

/-- Flat base change for scheme-theoretic images, stated for an arbitrary cartesian
square rather than for the chosen pullback. -/
theorem Scheme.Hom.ker_of_isPullback {Y' T' : Scheme.{u}} {q : Y' ⟶ Y} [Flat q]
    {p₁ : T' ⟶ T} {p₂ : T' ⟶ Y'} (H : IsPullback p₁ p₂ g q) :
    p₂.ker = g.ker.comap q := by
  rw [← H.isoPullback_hom_snd, Scheme.Hom.ker_comp_of_isIso, ker_pullback_snd]

/-- Restriction of a scheme-theoretic image to an open subscheme of the target: the
kernel of `g ∣_ U` is the restriction of the kernel of `g`. This is the special case of
`AlgebraicGeometry.Scheme.Hom.ker_of_isPullback` for the open immersion `U.ι`, which is
flat. (blueprint: `lemma:nagata-scheme-image-restrict-open`) -/
theorem Scheme.Hom.ker_morphismRestrict (U : Y.Opens) :
    (g ∣_ U).ker = g.ker.comap U.ι :=
  g.ker_of_isPullback (isPullback_morphismRestrict g U).flip

variable {Y' : Scheme.{u}} (q : Y' ⟶ Y) [Flat q]

/-- The two closed subschemes of `Y'` occurring in flat base change for
scheme-theoretic images have the same kernel ideal sheaf. -/
theorem Scheme.Hom.ker_pullback_fst_imageι :
    (pullback.fst q g.imageι).ker = (pullback.snd g q).imageι.ker := by
  rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.IdealSheafData.ker_subschemeι,
    Scheme.IdealSheafData.ker_subschemeι, ker_pullback_snd]

/-- Flat base change for scheme-theoretic images: for a quasi-compact morphism
`g : T ⟶ Y` and a flat `q : Y' ⟶ Y`, the scheme-theoretic image of the base change of
`g` to `Y'` is canonically isomorphic to the pullback of the scheme-theoretic image of
`g`, compatibly with the closed immersions into `Y'`
(`AlgebraicGeometry.Scheme.Hom.image.pullbackIso_hom_fst`) and with the factor maps
(`AlgebraicGeometry.Scheme.Hom.image.toImage_pullbackIso_hom_snd`). -/
def Scheme.Hom.image.pullbackIso : (pullback.snd g q).image ≅ pullback q g.imageι :=
  have := IsClosedImmersion.isIso_lift (pullback.fst q g.imageι) (pullback.snd g q).imageι
    (g.ker_pullback_fst_imageι q)
  asIso (IsClosedImmersion.lift (pullback.fst q g.imageι) (pullback.snd g q).imageι
    (g.ker_pullback_fst_imageι q).le)

@[reassoc (attr := simp)]
lemma Scheme.Hom.image.pullbackIso_hom_fst :
    (pullbackIso g q).hom ≫ pullback.fst q g.imageι = (pullback.snd g q).imageι :=
  IsClosedImmersion.lift_fac _ _ _

/-- The base change isomorphism is compatible with the factor maps through the
scheme-theoretic images. -/
@[reassoc (attr := simp)]
lemma Scheme.Hom.image.toImage_pullbackIso_hom_snd :
    (pullback.snd g q).toImage ≫ (pullbackIso g q).hom ≫ pullback.snd q g.imageι =
      pullback.fst g q ≫ g.toImage := by
  rw [← cancel_mono g.imageι]
  simp only [Category.assoc]
  rw [Scheme.Hom.toImage_imageι, ← pullback.condition, pullbackIso_hom_fst_assoc,
    Scheme.Hom.toImage_imageι_assoc, pullback.condition]

/-- Flat base change for scheme-theoretic images, in the form of a cartesian square:
for any `Zf` making the square commute, the closed immersion of the scheme-theoretic
image of the base change is the base change of the closed immersion of the
scheme-theoretic image of `g`. -/
lemma Scheme.Hom.image.isPullback_imageι (Zf : (pullback.snd g q).image ⟶ g.image)
    (h : (pullback.snd g q).imageι ≫ q = Zf ≫ g.imageι) :
    IsPullback (pullback.snd g q).imageι Zf q g.imageι :=
  isPullback_of_isClosedImmersion _ _ _ _ h <| by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
      ker_pullback_snd]

end AlgebraicGeometry
