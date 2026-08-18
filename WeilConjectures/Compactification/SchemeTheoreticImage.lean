/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib

/-!

# Scheme-theoretic images: the Nagata compactification interface

This file collects the scheme-theoretic image API needed for the proof of Nagata's
compactification theorem, following the blueprint chapter "Nagata compactification",
Section "Compactifications and scheme-theoretic images".

Mathlib already provides the scheme-theoretic image of a morphism `g : T ⟶ Y` as
`AlgebraicGeometry.Scheme.Hom.image`, the subscheme cut out by the kernel ideal sheaf
`g.ker`, together with the closed immersion `Scheme.Hom.imageι`, the factor map
`Scheme.Hom.toImage` and the factorization `Scheme.Hom.toImage_imageι` (blueprint
labels `lemma:nagata-scheme-image-ideal-qc` and `def:nagata-scheme-image-factor`).

We record here:

- `Nagata.schemeTheoreticImage`: notation for the Mathlib scheme-theoretic image
  (`def:nagata-scheme-theoretic-image`);
- `Nagata.schemeImageCompare` and `Nagata.schemeImageUniversal`: the universal property
  of the scheme-theoretic image among factorizations through closed immersions
  (`def:nagata-scheme-image-comparison`, `lemma:nagata-scheme-image-universal`);
- `Nagata.schemeImageFlatBaseChange`: formation of scheme-theoretic images commutes
  with flat base change for quasi-compact quasi-separated morphisms
  (`lemma:nagata-scheme-image-flat-base-change`, Stacks Project Tag 081I);
- `Nagata.schemeImageRestrictOpen`: the special case of restriction to an open
  subscheme of the target (`lemma:nagata-scheme-image-restrict-open`).

The flat base change lemma is proved by factoring the base-changed morphism through the
pullback of the scheme-theoretic image: the comparison map is the flat base change of
the scheme-theoretically dominant factor map `Scheme.Hom.toImage`, and Mathlib's
`AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isPullback` (which encapsulates the
affine kernel computations `lemma:nagata-affine-image-kernel-localization` and
`lemma:nagata-affine-image-kernel-flat` of the blueprint) shows it has trivial kernel.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Nagata

variable {T Y Z : Scheme.{u}}

/-- The scheme-theoretic image of a morphism `g : T ⟶ Y`, i.e. the closed subscheme of
`Y` cut out by the kernel ideal sheaf of `g`. This is Mathlib's `Scheme.Hom.image`; the
inclusion into `Y` is `g.imageι` and the factor map is `g.toImage`.
(Blueprint: `def:nagata-scheme-theoretic-image`.) -/
abbrev schemeTheoreticImage (g : T ⟶ Y) : Scheme.{u} :=
  g.image

section UniversalProperty

/-- If `g` factors through a closed immersion `z`, the kernel of `z` is contained in
the kernel of `g`. -/
lemma ker_le_ker_of_fac (g : T ⟶ Y) (h : T ⟶ Z) (z : Z ⟶ Y) (w : h ≫ z = g) :
    z.ker ≤ g.ker := by
  rw [← w]
  exact Scheme.Hom.le_ker_comp h z

/-- Given a factorization `g = h ≫ z` with `z : Z ⟶ Y` a closed immersion, the
canonical comparison map from the scheme-theoretic image of `g` to `Z`.
(Blueprint: `def:nagata-scheme-image-comparison`.) -/
def schemeImageCompare (g : T ⟶ Y) (h : T ⟶ Z) (z : Z ⟶ Y) [IsClosedImmersion z]
    (w : h ≫ z = g) : g.image ⟶ Z :=
  IsClosedImmersion.lift z g.imageι (by simpa using ker_le_ker_of_fac g h z w)

@[reassoc (attr := simp)]
lemma schemeImageCompare_comp (g : T ⟶ Y) (h : T ⟶ Z) (z : Z ⟶ Y) [IsClosedImmersion z]
    (w : h ≫ z = g) : schemeImageCompare g h z w ≫ z = g.imageι :=
  IsClosedImmersion.lift_fac _ _ _

/-- The comparison map from the scheme-theoretic image to a closed factorization is a
closed immersion. -/
lemma isClosedImmersion_schemeImageCompare (g : T ⟶ Y) (h : T ⟶ Z) (z : Z ⟶ Y)
    [IsClosedImmersion z] (w : h ≫ z = g) :
    IsClosedImmersion (schemeImageCompare g h z w) :=
  have : IsClosedImmersion (schemeImageCompare g h z w ≫ z) := by
    rw [schemeImageCompare_comp]
    infer_instance
  IsClosedImmersion.of_comp_isClosedImmersion _ z

/-- The comparison map is the unique morphism from the scheme-theoretic image which is
compatible with the maps to the common target. -/
lemma schemeImageCompare_unique (g : T ⟶ Y) (h : T ⟶ Z) (z : Z ⟶ Y) [IsClosedImmersion z]
    (w : h ≫ z = g) (c : g.image ⟶ Z) (hc : c ≫ z = g.imageι) :
    c = schemeImageCompare g h z w := by
  rw [← cancel_mono z, hc, schemeImageCompare_comp]

/-- Universal property of the scheme-theoretic image: for every factorization of `g`
through a closed immersion `z : Z ⟶ Y` there is a unique morphism from the
scheme-theoretic image of `g` to `Z` compatible with the maps to `Y`. The morphism is
the closed immersion `Nagata.schemeImageCompare`; the factorization of `g` through its
scheme-theoretic image is `Scheme.Hom.toImage_imageι`.
(Blueprint: `lemma:nagata-scheme-image-universal`.) -/
theorem schemeImageUniversal (g : T ⟶ Y) (h : T ⟶ Z) (z : Z ⟶ Y) [IsClosedImmersion z]
    (w : h ≫ z = g) : ∃! c : g.image ⟶ Z, c ≫ z = g.imageι :=
  ⟨schemeImageCompare g h z w, schemeImageCompare_comp g h z w,
    fun c hc ↦ schemeImageCompare_unique g h z w c hc⟩

end UniversalProperty

section BaseChange

/-- The inclusions of the subschemes attached to equal ideal sheaves agree up to
`eqToHom`. -/
lemma subschemeι_eqToHom {I J : Y.IdealSheafData} (e : I = J) :
    eqToHom (congrArg Scheme.IdealSheafData.subscheme e) ≫ J.subschemeι =
      I.subschemeι := by
  subst e
  simp

/-- The factor map `g.toImage : T ⟶ SIm(g)` through the scheme-theoretic image of a
quasi-compact morphism is scheme-theoretically dominant: its kernel ideal sheaf vanishes.
This is checked on the affine cover of the image obtained by pulling back the affine
opens of `Y` along the closed immersion `g.imageι`, where the section map is injective
by `Scheme.Hom.toImage_app_injective`. -/
instance (g : T ⟶ Y) [QuasiCompact g] : IsSchemeTheoreticallyDominant g.toImage := by
  refine ⟨Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens ↦ ⟨g.imageι ⁻¹ᵁ U.1, U.2.preimage g.imageι⟩)
    (g.imageι.iSup_preimage_eq_top (iSup_affineOpens_eq_top Y)) fun U ↦ ?_⟩
  simp only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (g.toImage_app_injective U)

variable (g : T ⟶ Y) [QuasiCompact g]

/-- Flat base change for scheme-theoretic images, in kernel ideal sheaf form: for a
quasi-compact morphism `g : T ⟶ Y` and a flat morphism `q : Y' ⟶ Y`, the kernel of the
base change `T ×_Y Y' ⟶ Y'` is the pullback of the kernel of `g`.
(Blueprint: `lemma:nagata-scheme-image-flat-base-change`; Stacks Project Tag 081I. The
blueprint and the Stacks Project assume `g` quasi-separated as well, but Mathlib's
kernel ideal sheaf theory only needs quasi-compactness.)

The proof factors the base change `T ×_Y Y' ⟶ Y'` through `SIm(g) ×_Y Y'`: the first
factor is the flat base change of the scheme-theoretically dominant map `g.toImage`,
hence is itself scheme-theoretically dominant
(`AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isPullback`), so the kernel is
that of the closed immersion `SIm(g) ×_Y Y' ⟶ Y'`, which is `g.ker.comap q` by
definition of the pullback of ideal sheaves. -/
theorem schemeImageFlatBaseChange {Y' : Scheme.{u}} (q : Y' ⟶ Y) [Flat q] :
    (pullback.snd g q).ker = g.ker.comap q := by
  have w : pullback.snd g q ≫ q = (pullback.fst g q ≫ g.toImage) ≫ g.imageι := by
    rw [Category.assoc, g.toImage_imageι, pullback.condition]
  -- The comparison map `T ×_Y Y' ⟶ SIm(g) ×_Y Y'` is the base change of `g.toImage`
  -- along the flat projection `SIm(g) ×_Y Y' ⟶ SIm(g)`.
  have hsq : IsPullback (pullback.lift (pullback.snd g q) (pullback.fst g q ≫ g.toImage) w)
      (pullback.fst g q) (pullback.snd q g.imageι) g.toImage := by
    refine .of_right ?_ (pullback.lift_snd _ _ _) (.of_hasPullback q g.imageι)
    rw [pullback.lift_fst, g.toImage_imageι]
    exact (IsPullback.of_hasPullback g q).flip
  have : IsSchemeTheoreticallyDominant
      (pullback.lift (pullback.snd g q) (pullback.fst g q ≫ g.toImage) w) :=
    .of_isPullback hsq.flip
  rw [← pullback.lift_fst (pullback.snd g q) (pullback.fst g q ≫ g.toImage) w,
    Scheme.Hom.ker_comp,
    Scheme.Hom.ker_eq_bot (pullback.lift (pullback.snd g q) (pullback.fst g q ≫ g.toImage) w),
    Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    Scheme.IdealSheafData.ker_subschemeι]

/-- Flat base change for scheme-theoretic images: for a quasi-compact quasi-separated
morphism `g : T ⟶ Y` and a flat `q : Y' ⟶ Y`, the scheme-theoretic image of the base
change of `g` to `Y'` is canonically isomorphic to the pullback of the scheme-theoretic
image of `g`, compatibly with the closed immersions into `Y'`
(`Nagata.schemeImageFlatBaseChangeIso_hom_fst`). -/
def schemeImageFlatBaseChangeIso {Y' : Scheme.{u}} (q : Y' ⟶ Y) [Flat q] :
    (pullback.snd g q).image ≅ pullback q g.imageι :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme (schemeImageFlatBaseChange g q)) ≪≫
    g.ker.comapIso q

@[reassoc (attr := simp)]
lemma schemeImageFlatBaseChangeIso_hom_fst {Y' : Scheme.{u}} (q : Y' ⟶ Y) [Flat q] :
    (schemeImageFlatBaseChangeIso g q).hom ≫ pullback.fst q g.imageι =
      (pullback.snd g q).imageι := by
  simp only [schemeImageFlatBaseChangeIso, Iso.trans_hom, eqToIso.hom, Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]
  exact subschemeι_eqToHom (schemeImageFlatBaseChange g q)

/-- Restriction of a scheme-theoretic image to an open subscheme `j : W ⟶ Y` of the
target, in kernel ideal sheaf form. Open immersions are flat, so this is a special case
of flat base change. On affine opens the right hand side is computed by
`Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion`.
(Blueprint: `lemma:nagata-scheme-image-restrict-open`.) -/
theorem schemeImageRestrictOpen {W : Scheme.{u}} (j : W ⟶ Y) [IsOpenImmersion j] :
    (pullback.snd g j).ker = g.ker.comap j :=
  schemeImageFlatBaseChange g j

/-- Restriction of a scheme-theoretic image to an open subscheme of the target: the
scheme-theoretic image of the restriction `T ×_Y W ⟶ W` is canonically isomorphic to
the pullback of the scheme-theoretic image of `g`, compatibly with the inclusions
into `W`. -/
def schemeImageRestrictOpenIso {W : Scheme.{u}} (j : W ⟶ Y) [IsOpenImmersion j] :
    (pullback.snd g j).image ≅ pullback j g.imageι :=
  schemeImageFlatBaseChangeIso g j

@[reassoc (attr := simp)]
lemma schemeImageRestrictOpenIso_hom_fst {W : Scheme.{u}} (j : W ⟶ Y)
    [IsOpenImmersion j] :
    (schemeImageRestrictOpenIso g j).hom ≫ pullback.fst j g.imageι =
      (pullback.snd g j).imageι :=
  schemeImageFlatBaseChangeIso_hom_fst g j

end BaseChange

end AlgebraicGeometry.Nagata
