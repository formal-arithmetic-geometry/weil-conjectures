/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Scheme-theoretically dominant morphisms

Complements to Mathlib's `IsSchemeTheoreticallyDominant`, in four independent groups.

## Flat base change for scheme-theoretic images

Formation of scheme-theoretic images commutes with flat base change (blueprint:
`lemma:nagata-scheme-image-flat-base-change`; Stacks Project Tag 081I):

- `AlgebraicGeometry.isSchemeTheoreticallyDominant_iff_isIso_imageι`: a morphism is
  scheme-theoretically dominant if and only if the inclusion of its scheme-theoretic
  image is an isomorphism;
- `AlgebraicGeometry.Scheme.Hom.ker_pullback_snd` and
  `AlgebraicGeometry.Scheme.Hom.ker_of_isPullback`: for `q : Y' ⟶ Y` flat, the kernel of
  the base change `T ×_Y Y' ⟶ Y'` is the pullback of the kernel of `g`;
- `AlgebraicGeometry.Scheme.Hom.image.pullbackIso`: the scheme-theoretic image of the
  base change is canonically isomorphic to the pullback of the scheme-theoretic image,
  compatibly with the closed immersions into `Y'`
  (`AlgebraicGeometry.Scheme.Hom.image.pullbackIso_hom_fst`) and with the factor maps
  (`AlgebraicGeometry.Scheme.Hom.image.toImage_pullbackIso_hom_snd`); it is the unique
  such isomorphism (`AlgebraicGeometry.Scheme.Hom.image.eq_pullbackIso_hom`), and
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

## Scheme-theoretically dominant open subschemes

Permanence properties of scheme-theoretically dense opens, i.e. opens `U ⊆ X` whose
inclusion `U.ι` is scheme-theoretically dominant:

- `AlgebraicGeometry.IsSchemeTheoreticallyDominant.homOfLE`: if `U ≤ W` and `U` is
  scheme-theoretically dense in `X`, then the inclusion `U ⟶ W` of the intermediate
  open subscheme is scheme-theoretically dominant;
- `AlgebraicGeometry.IsSchemeTheoreticallyDominant.preimage_ι_of_le`: if `f : X' ⟶ X`
  restricts to an isomorphism over `W`, the open `f ⁻¹ᵁ W` is scheme-theoretically
  dense in `X'` and `U ≤ W` is scheme-theoretically dense in `X`, then `f ⁻¹ᵁ U` is
  scheme-theoretically dense in `X'`.

## Rigidity of morphisms into a separated scheme

`AlgebraicGeometry.ext_of_isSchemeTheoreticallyDominant`: two `S`-morphisms `a b : T ⟶ Y`
into a scheme `Y` separated over `S` are equal as soon as they agree after composing with
a scheme-theoretically dominant morphism `v : V ⟶ T` (blueprint:
`lem:chow-agree-on-dense-open`; Stacks Project Tag 01RH). Taking `v = V.ι` for a
scheme-theoretically dense open `V ⊆ T` gives the form in which the statement is usually
quoted, and combining it with
`AlgebraicGeometry.IsSchemeTheoreticallyDominant.homOfLE` lets one test equality of
morphisms defined on an intermediate open `W` on a scheme-theoretically dense open
`V ≤ W`.

## Kernels along scheme-theoretically dominant morphisms

`AlgebraicGeometry.Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant`: precomposing with a
quasi-compact scheme-theoretically dominant morphism does not change the kernel. This is what
lets the universal property of a closed immersion be applied after replacing a morphism by its
restriction to a scheme-theoretically dense open.
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

variable (g : T ⟶ Y) [QuasiCompact g] {Y' : Scheme.{u}} (q : Y' ⟶ Y) [Flat q]

/-- Flat base change for scheme-theoretic images, in kernel ideal sheaf form: for a
quasi-compact morphism `g : T ⟶ Y` and a flat morphism `q : Y' ⟶ Y`, the kernel of the
base change `T ×_Y Y' ⟶ Y'` is the pullback of the kernel of `g`.
(blueprint: `lemma:nagata-scheme-image-flat-base-change`; Stacks Project Tag 081I. The
blueprint and the Stacks Project assume `g` quasi-separated as well, but Mathlib's
kernel ideal sheaf theory only needs quasi-compactness.) -/
theorem Scheme.Hom.ker_pullback_snd : (pullback.snd g q).ker = g.ker.comap q := by
  have w : pullback.snd g q ≫ q = (pullback.fst g q ≫ g.toImage) ≫ g.imageι := by
    rw [Category.assoc, g.toImage_imageι, pullback.condition]
  -- Factor the base change `T ×_Y Y' ⟶ Y'` through the closed subscheme
  -- `g.image ×_Y Y' ⟶ Y'` via `c`.
  set c := pullback.lift (pullback.snd g q) (pullback.fst g q ≫ g.toImage) w with hc
  have hfst : c ≫ pullback.fst q g.imageι = pullback.snd g q := pullback.lift_fst _ _ _
  -- `c` is the base change of `g.toImage` along the projection `g.image ×_Y Y' ⟶ g.image`,
  -- hence is scheme-theoretically dominant because `g.toImage` is and `q` is flat.
  have hsq : IsPullback c (pullback.fst g q) (pullback.snd q g.imageι) g.toImage := by
    refine .of_right ?_ (pullback.lift_snd _ _ _) (.of_hasPullback q g.imageι)
    rw [hc, pullback.lift_fst, g.toImage_imageι]
    exact (IsPullback.of_hasPullback g q).flip
  have : IsSchemeTheoreticallyDominant c := .of_isPullback hsq.flip
  -- So the kernel of the base change is the kernel of the closed immersion
  -- `g.image ×_Y Y' ⟶ Y'`, which is `g.ker.comap q` by definition.
  rw [← hfst, Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot c, Scheme.IdealSheafData.map_bot,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.IdealSheafData.ker_subschemeι]

/-- Flat base change for scheme-theoretic images, stated for an arbitrary cartesian
square rather than for the chosen pullback. -/
theorem Scheme.Hom.ker_of_isPullback {T' : Scheme.{u}} {p₁ : T' ⟶ T} {p₂ : T' ⟶ Y'}
    (H : IsPullback p₁ p₂ g q) : p₂.ker = g.ker.comap q := by
  rw [← H.isoPullback_hom_snd, Scheme.Hom.ker_comp_of_isIso, ker_pullback_snd]

/-- Restriction of a scheme-theoretic image to an open subscheme of the target: the
kernel of `g ∣_ U` is the restriction of the kernel of `g`. This is the special case of
`AlgebraicGeometry.Scheme.Hom.ker_of_isPullback` for the open immersion `U.ι`, which is
flat. (blueprint: `lemma:nagata-scheme-image-restrict-open`) -/
theorem Scheme.Hom.ker_morphismRestrict (U : Y.Opens) :
    (g ∣_ U).ker = g.ker.comap U.ι :=
  g.ker_of_isPullback U.ι (isPullback_morphismRestrict g U).flip

/-- The two closed subschemes of `Y'` occurring in flat base change for
scheme-theoretic images have the same kernel ideal sheaf.

For `q` an open immersion this is
`AlgebraicGeometry.Scheme.ker_imageι_pullback_snd`, up to swapping the two factors of
the pullback. -/
theorem Scheme.Hom.ker_pullback_fst_imageι :
    (pullback.fst q g.imageι).ker = (pullback.snd g q).imageι.ker := by
  rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.IdealSheafData.ker_subschemeι,
    Scheme.IdealSheafData.ker_subschemeι, ker_pullback_snd]

/-- Flat base change for scheme-theoretic images: for a quasi-compact morphism
`g : T ⟶ Y` and a flat `q : Y' ⟶ Y`, the scheme-theoretic image of the base change of
`g` to `Y'` is canonically isomorphic to the pullback of the scheme-theoretic image of
`g`, compatibly with the closed immersions into `Y'`
(`AlgebraicGeometry.Scheme.Hom.image.pullbackIso_hom_fst`) and with the factor maps
(`AlgebraicGeometry.Scheme.Hom.image.toImage_pullbackIso_hom_snd`). It is the unique
isomorphism over `Y'`, see
`AlgebraicGeometry.Scheme.Hom.image.eq_pullbackIso_hom`. -/
def Scheme.Hom.image.pullbackIso : (pullback.snd g q).image ≅ pullback q g.imageι :=
  have := IsClosedImmersion.isIso_lift (pullback.fst q g.imageι) (pullback.snd g q).imageι
    (g.ker_pullback_fst_imageι q)
  asIso (IsClosedImmersion.lift (pullback.fst q g.imageι) (pullback.snd g q).imageι
    (g.ker_pullback_fst_imageι q).le)

@[reassoc (attr := simp)]
lemma Scheme.Hom.image.pullbackIso_hom_fst :
    (pullbackIso g q).hom ≫ pullback.fst q g.imageι = (pullback.snd g q).imageι :=
  IsClosedImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
lemma Scheme.Hom.image.pullbackIso_inv_imageι :
    (pullbackIso g q).inv ≫ (pullback.snd g q).imageι = pullback.fst q g.imageι := by
  rw [Iso.inv_comp_eq, pullbackIso_hom_fst]

/-- The base change isomorphism is the unique morphism over `Y'`, since both closed
immersions into `Y'` are monomorphisms. -/
lemma Scheme.Hom.image.eq_pullbackIso_hom (c : (pullback.snd g q).image ⟶ pullback q g.imageι)
    (hc : c ≫ pullback.fst q g.imageι = (pullback.snd g q).imageι) :
    c = (pullbackIso g q).hom := by
  rw [← cancel_mono (pullback.fst q g.imageι), hc, pullbackIso_hom_fst]

/-- The base change isomorphism is compatible with the factor maps through the
scheme-theoretic images. -/
@[reassoc (attr := simp)]
lemma Scheme.Hom.image.toImage_pullbackIso_hom_snd :
    (pullback.snd g q).toImage ≫ (pullbackIso g q).hom ≫ pullback.snd q g.imageι =
      pullback.fst g q ≫ g.toImage := by
  rw [← cancel_mono g.imageι, Category.assoc, Category.assoc, Category.assoc,
    -- cross the square `pullback q g.imageι` from `pullback.snd` to `pullback.fst`, ...
    ← pullback.condition (f := q) (g := g.imageι), pullbackIso_hom_fst_assoc,
    Scheme.Hom.toImage_imageι_assoc, Scheme.Hom.toImage_imageι,
    -- ... and cross the *other* square `pullback g q` in the opposite direction
    pullback.condition (f := g) (g := q)]

/-- Flat base change for scheme-theoretic images in the form of a cartesian square, for
an arbitrary morphism `f'` making the square commute rather than the canonical one used
in `AlgebraicGeometry.Scheme.Hom.image.isPullback_imageι`. -/
lemma Scheme.Hom.image.isPullback_imageι_of_comp (f' : (pullback.snd g q).image ⟶ g.image)
    (h : (pullback.snd g q).imageι ≫ q = f' ≫ g.imageι) :
    IsPullback (pullback.snd g q).imageι f' q g.imageι :=
  isPullback_of_isClosedImmersion _ _ _ _ h <| by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
      ker_pullback_snd]

/-- Flat base change for scheme-theoretic images, in the form of a cartesian square: the
closed immersion of the scheme-theoretic image of the base change is the base change of
the closed immersion of the scheme-theoretic image of `g`:

```
  im (X ×_Y Y' ⟶ Y') --------> im (X ⟶ Y)
          |                         |
       imageι                    imageι
          ↓                         ↓
          Y' ---------- q ---------> Y
```
-/
lemma Scheme.Hom.image.isPullback_imageι :
    IsPullback (pullback.snd g q).imageι ((pullbackIso g q).hom ≫ pullback.snd q g.imageι)
      q g.imageι :=
  isPullback_imageι_of_comp g q _ <| by
    rw [← pullbackIso_hom_fst_assoc, pullback.condition, Category.assoc]

section Opens

variable {X' X : Scheme.{u}}

/-- If `U ≤ W` are opens of `X` with `U` scheme-theoretically dense in `X`, then the
inclusion of `U` into the intermediate open subscheme `W` is scheme-theoretically
dominant. -/
theorem IsSchemeTheoreticallyDominant.homOfLE {U W : X.Opens} (h : U ≤ W)
    [QuasiCompact U.ι] [IsSchemeTheoreticallyDominant U.ι] :
    IsSchemeTheoreticallyDominant (X.homOfLE h) := by
  have hd : IsSchemeTheoreticallyDominant (X.homOfLE (inf_le_right : U ⊓ W ≤ W)) :=
    .of_isPullback (isPullback_opens_inf U W)
  have he : X.homOfLE h =
      (X.isoOfEq (inf_eq_left.mpr h)).inv ≫ X.homOfLE (inf_le_right : U ⊓ W ≤ W) := by
    rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι,
      Scheme.isoOfEq_inv_ι]
  rw [he]
  infer_instance

/-- The restriction of `f` to an open `U ≤ W` is an isomorphism whenever the
restriction of `f` to `W` is. -/
theorem isIso_morphismRestrict_of_le (f : X' ⟶ X) {U W : X.Opens} (h : U ≤ W)
    (hW : IsIso (f ∣_ W)) : IsIso (f ∣_ U) := by
  have himg : W.ι ''ᵁ (W.ι ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr h]
  have hiso : IsIso ((f ∣_ W) ∣_ (W.ι ⁻¹ᵁ U)) := inferInstance
  exact (MorphismProperty.arrow_mk_iso_iff (.isomorphisms Scheme)
    (morphismRestrictRestrict f W (W.ι ⁻¹ᵁ U) ≪≫ morphismRestrictEq f himg)).mp hiso

/-- **Scheme-theoretic density descends along partial isomorphisms**: let
`f : X' ⟶ X` be a morphism restricting to an isomorphism over an open `W ⊆ X` whose
preimage is scheme-theoretically dense in `X'`. Then the preimage of any
scheme-theoretically dense open `U ≤ W` of `X` is scheme-theoretically dense
in `X'`. -/
theorem IsSchemeTheoreticallyDominant.preimage_ι_of_le (f : X' ⟶ X) {U W : X.Opens}
    (hUW : U ≤ W) [QuasiCompact U.ι] [IsSchemeTheoreticallyDominant U.ι]
    (hW : IsIso (f ∣_ W)) [IsSchemeTheoreticallyDominant (f ⁻¹ᵁ W).ι] :
    IsSchemeTheoreticallyDominant (f ⁻¹ᵁ U).ι := by
  have hU : IsIso (f ∣_ U) := isIso_morphismRestrict_of_le f hUW hW
  have := hW
  have hpre : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ W := f.preimage_mono hUW
  -- the square `(f ∣_ U) ≫ homOfLE hUW = homOfLE hpre ≫ (f ∣_ W)`
  have hsq : X'.homOfLE hpre = (f ∣_ U) ≫ X.homOfLE hUW ≫ inv (f ∣_ W) := by
    rw [eq_comm, ← Category.assoc, IsIso.comp_inv_eq, ← cancel_mono W.ι]
    simp [morphismRestrict_ι, Scheme.homOfLE_ι_assoc, Scheme.homOfLE_ι]
  have : IsSchemeTheoreticallyDominant (X.homOfLE hUW) := .homOfLE hUW
  have : IsSchemeTheoreticallyDominant (X'.homOfLE hpre) := by
    rw [hsq]
    infer_instance
  have he : (f ⁻¹ᵁ U).ι = X'.homOfLE hpre ≫ (f ⁻¹ᵁ W).ι := (Scheme.homOfLE_ι _ _).symm
  rw [he]
  infer_instance

end Opens

section Separated

/-- **Rigidity of morphisms into a separated scheme**: if `Y` is separated over `S`, then
two `S`-morphisms `a b : T ⟶ Y` that agree after composing with a scheme-theoretically
dominant morphism `v : V ⟶ T` are equal. The classical case is `v = V.ι` for a
scheme-theoretically dense open subscheme `V ⊆ T`.

The equaliser of `a` and `b` is the base change of the diagonal `Y ⟶ Y ×[S] Y` along
`(a, b) : T ⟶ Y ×[S] Y`, hence a *closed* subscheme of `T` because `Y ⟶ S` is separated.
As `v` factors through it, its kernel ideal sheaf is contained in the kernel of `v`, which
is trivial; so the closed immersion is an isomorphism, in particular an epimorphism, and
`a = b`. (blueprint: `lem:chow-agree-on-dense-open`) -/
@[stacks 01RH]
theorem ext_of_isSchemeTheoreticallyDominant {V T Y S : Scheme.{u}} (g : Y ⟶ S)
    [IsSeparated g] {a b : T ⟶ Y} (h : a ≫ g = b ≫ g) (v : V ⟶ T)
    [IsSchemeTheoreticallyDominant v] (hab : v ≫ a = v ≫ b) : a = b := by
  -- `p = (a, b) : T ⟶ Y ×[S] Y` and `z` is the equaliser of `a` and `b`, realised as the
  -- base change of the diagonal of `g` along `p`.
  set p : T ⟶ pullback g g := pullback.lift a b h with hp
  set z : pullback p (pullback.diagonal g) ⟶ T := pullback.fst p (pullback.diagonal g) with hz
  have : IsClosedImmersion z := by
    rw [hz]
    infer_instance
  -- `a` and `b` agree after composing with `z`, both projections being the second
  -- projection of the defining square.
  have hpa : a = p ≫ pullback.fst g g := (pullback.lift_fst _ _ _).symm
  have hpb : b = p ≫ pullback.snd g g := (pullback.lift_snd _ _ _).symm
  have hza : z ≫ a = pullback.snd p (pullback.diagonal g) := by
    rw [hpa, ← Category.assoc, hz, pullback.condition, Category.assoc, pullback.diagonal_fst,
      Category.comp_id]
  have hzb : z ≫ b = pullback.snd p (pullback.diagonal g) := by
    rw [hpb, ← Category.assoc, hz, pullback.condition, Category.assoc, pullback.diagonal_snd,
      Category.comp_id]
  -- `v` factors through `z`, because `a` and `b` agree after composing with `v`.
  have hcomm : v ≫ p = (v ≫ a) ≫ pullback.diagonal g :=
    pullback.hom_ext
      (by rw [hp, Category.assoc, pullback.lift_fst, Category.assoc,
        pullback.diagonal_fst, Category.comp_id])
      (by rw [hp, Category.assoc, pullback.lift_snd, Category.assoc,
        pullback.diagonal_snd, Category.comp_id, hab])
  have hfac : pullback.lift _ _ hcomm ≫ z = v := pullback.lift_fst _ _ _
  -- Hence the kernel of `z` is contained in the trivial kernel of `v`, so `z` is an
  -- isomorphism.
  have : IsIso z := by
    rw [IsClosedImmersion.isIso_iff_ker_eq_bot]
    refine le_bot_iff.mp ?_
    rw [← v.ker_eq_bot, ← hfac]
    exact Scheme.Hom.le_ker_comp _ _
  rw [← cancel_epi z, hza, hzb]

end Separated

section Kernel

variable {X Y Z : Scheme.{u}}

/-- Precomposing with a quasi-compact scheme-theoretically dominant morphism does not
change the kernel: if `d : X ⟶ Y` is scheme-theoretically dominant and quasi-compact,
then `(d ≫ h).ker = h.ker` for every `h : Y ⟶ Z`. -/
lemma Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant (d : X ⟶ Y) (h : Y ⟶ Z)
    [IsSchemeTheoreticallyDominant d] [QuasiCompact d] :
    (d ≫ h).ker = h.ker := by
  -- only the inequality `(d ≫ h).ker ≤ h.ker` is content, the other one being
  -- `AlgebraicGeometry.Scheme.Hom.le_ker_comp`: sections of `𝒪_Z` killed by `d ≫ h` are
  -- already killed by `h`, since each `d.app` is injective
  have key (U : Z.affineOpens) :
      RingHom.ker ((d ≫ h).app U).hom = RingHom.ker ((h.app U).hom) := by
    rw [Scheme.Hom.comp_app, CommRingCat.hom_comp,
      RingHom.ker_comp_of_injective _ (d.app_injective _)]
  simp only [Scheme.Hom.ker, key]

end Kernel

end AlgebraicGeometry
