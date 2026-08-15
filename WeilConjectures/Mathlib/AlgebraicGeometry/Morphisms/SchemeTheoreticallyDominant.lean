/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Flat base change for scheme-theoretic images

We show that the factor map `g.toImage : T ⟶ g.image` through the scheme-theoretic
image of a quasi-compact morphism `g : T ⟶ Y` is scheme-theoretically dominant, and
deduce that formation of scheme-theoretic images commutes with flat base change
(blueprint label `lemma:nagata-scheme-image-flat-base-change`, Stacks Project Tag 081I):

- `AlgebraicGeometry.Scheme.Hom.ker_pullback_snd`: for `q : Y' ⟶ Y` flat, the kernel of
  the base change `T ×_Y Y' ⟶ Y'` is the pullback of the kernel of `g`;
- `AlgebraicGeometry.Scheme.Hom.image.pullbackIso`: the scheme-theoretic image of the
  base change is canonically isomorphic to the pullback of the scheme-theoretic image,
  compatibly with the closed immersions into `Y'`
  (`AlgebraicGeometry.Scheme.Hom.image.pullbackIso_hom_fst`).

The proof factors the base-changed morphism through the pullback of the
scheme-theoretic image: the comparison map is the flat base change of the
scheme-theoretically dominant factor map `Scheme.Hom.toImage`, and Mathlib's
`AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isPullback` (which encapsulates the
affine kernel computations `lemma:nagata-affine-image-kernel-localization` and
`lemma:nagata-affine-image-kernel-flat` of the blueprint) shows it has trivial kernel.

Restriction to an open subscheme of the target
(`lemma:nagata-scheme-image-restrict-open`) is the special case of an open immersion
`q`, which is flat.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {T Y : Scheme.{u}}

/-- The factor map `g.toImage : T ⟶ g.image` through the scheme-theoretic image of a
quasi-compact morphism is scheme-theoretically dominant: its kernel ideal sheaf
vanishes. This is checked on the affine cover of the image obtained by pulling back the
affine opens of `Y` along the closed immersion `g.imageι`, where the section map is
injective by `Scheme.Hom.toImage_app_injective`. -/
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

/-- Flat base change for scheme-theoretic images: for a quasi-compact morphism
`g : T ⟶ Y` and a flat `q : Y' ⟶ Y`, the scheme-theoretic image of the base change of
`g` to `Y'` is canonically isomorphic to the pullback of the scheme-theoretic image of
`g`, compatibly with the closed immersions into `Y'`
(`AlgebraicGeometry.Scheme.Hom.image.pullbackIso_hom_fst`). -/
def Scheme.Hom.image.pullbackIso {Y' : Scheme.{u}} (q : Y' ⟶ Y) [Flat q] :
    (pullback.snd g q).image ≅ pullback q g.imageι :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme (Scheme.Hom.ker_pullback_snd g q)) ≪≫
    g.ker.comapIso q

@[reassoc (attr := simp)]
lemma Scheme.Hom.image.pullbackIso_hom_fst {Y' : Scheme.{u}} (q : Y' ⟶ Y) [Flat q] :
    (pullbackIso g q).hom ≫ pullback.fst q g.imageι = (pullback.snd g q).imageι := by
  simp only [pullbackIso, Iso.trans_hom, eqToIso.hom, Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]
  exact Scheme.IdealSheafData.eqToHom_comp_subschemeι (Scheme.Hom.ker_pullback_snd g q)

end AlgebraicGeometry
