/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Two complements on the scheme-theoretic image

Mathlib has the scheme-theoretic image `AlgebraicGeometry.Scheme.Hom.image` of a morphism,
its closed immersion `imageι` into the target and the factorization
`toImage_imageι : f.toImage ≫ f.imageι = f`. This file adds the two statements about it that
the Nagata compactification blueprint needs and that Mathlib does not have.

## Main results

- `AlgebraicGeometry.Scheme.Hom.isPullback_id_toImage`: the square

  ```
  X  --𝟙-->  X
  |          |
  toImage    f
  v          v
  f.image --imageι--> Y
  ```

  is cartesian, so `f.toImage` is the base change of `f` along `f.imageι`
  (blueprint: `lemma:nagata-scheme-image-factor-cartesian`). This is not
  `AlgebraicGeometry.IsImmersion.isPullback_toImage_liftCoborder`, whose lower-left corner is
  a coborder range rather than `X`.

- `AlgebraicGeometry.Scheme.imageRestrictIso`: for quasi-compact `g : T ⟶ Y` and an open
  immersion `w : W ⟶ Y`, the scheme-theoretic image of the base change `g_W : T ×_Y W ⟶ W` is
  the base change of the scheme-theoretic image, compatibly with the two factorizations
  (blueprint: `lemma:nagata-scheme-image-restrict-open`).

## Implementation notes

Both proofs reduce to statements that are already in Mathlib, which is why this file is short.

The cartesian square is not a scheme-theoretic fact at all: for *any* monomorphism `i` and any
factorization `f = t ≫ i`, the square with top edge `𝟙` is cartesian, and that is
`CategoryTheory.IsPullback.of_horiz_isIso_mono`. Here `i = f.imageι` is a closed immersion,
hence a preimmersion, hence a monomorphism.

The restriction statement reduces to an equality of ideal sheaves, because two closed
immersions into the same scheme with the same kernel are canonically isomorphic
(`AlgebraicGeometry.IsClosedImmersion.isIso_lift`). That equality in turn is
`AlgebraicGeometry.Scheme.ker_ideal_of_isPullback_of_isOpenImmersion` applied twice — once to
`g` and once to `g.imageι` — since the two applications produce literally the same formula,
`g.imageι` having the same kernel as `g` by
`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/-! ### The cartesian square defined by the scheme-image factor -/

/-- **The scheme-theoretic image factorization is cartesian.** The square

```
X  --𝟙-->  X
|          |
toImage    f
v          v
f.image --imageι--> Y
```

is a pullback square, so `f.toImage` is the base change of `f` along `f.imageι`.

There is nothing scheme-theoretic here: `f.imageι` is a monomorphism and `f` factors through
it, and for any monomorphism the square with top edge the identity is cartesian.

(blueprint: `lemma:nagata-scheme-image-factor-cartesian`) -/
lemma Hom.isPullback_id_toImage (f : X ⟶ Y) :
    IsPullback (𝟙 X) f.toImage f f.imageι :=
  IsPullback.of_horiz_isIso_mono ⟨by simp⟩

/-! ### Restriction of a scheme-theoretic image to an open of the target -/

section RestrictOpen

variable {T W : Scheme.{u}} (g : T ⟶ Y) [QuasiCompact g] (w : W ⟶ Y) [IsOpenImmersion w]

/-- **Taking the scheme-theoretic image commutes with restriction to an open of the target,
at the level of ideal sheaves.** The kernel of the base change of `g` along an open immersion
`w` is the kernel of the base change of the closed immersion `g.imageι` along `w`.

Both sides are computed by `AlgebraicGeometry.Scheme.ker_ideal_of_isPullback_of_isOpenImmersion`
into the same expression, because `g.imageι` has the same kernel as `g`. -/
lemma ker_pullback_snd_eq_ker_pullback_snd_imageι :
    (pullback.snd g w).ker = (pullback.snd g.imageι w).ker := by
  ext V
  rw [ker_ideal_of_isPullback_of_isOpenImmersion g (pullback.snd g w) (pullback.fst g w) w
      (IsPullback.of_hasPullback g w).flip V,
    ker_ideal_of_isPullback_of_isOpenImmersion g.imageι (pullback.snd g.imageι w)
      (pullback.fst g.imageι w) w (IsPullback.of_hasPullback g.imageι w).flip V,
    IdealSheafData.ker_subschemeι]

/-- The closed immersion of the scheme-theoretic image of the base change has the same kernel
as the base change of the closed immersion of the scheme-theoretic image. This is the input to
`AlgebraicGeometry.IsClosedImmersion.isIso_lift` that produces
`AlgebraicGeometry.Scheme.imageRestrictIso`. -/
lemma ker_imageι_pullback_snd :
    (pullback.snd g w).imageι.ker = (pullback.snd g.imageι w).ker := by
  rw [IdealSheafData.ker_subschemeι, ker_pullback_snd_eq_ker_pullback_snd_imageι]

/-- The comparison morphism from the scheme-theoretic image of the base change `g_W` to the
base change of the scheme-theoretic image of `g`. It is an isomorphism, see
`AlgebraicGeometry.Scheme.imageRestrictIso`. -/
noncomputable def imageRestrictHom :
    (pullback.snd g w).image ⟶ pullback g.imageι w :=
  IsClosedImmersion.lift (pullback.snd g.imageι w) (pullback.snd g w).imageι
    (ker_imageι_pullback_snd g w).ge

@[reassoc (attr := simp)]
lemma imageRestrictHom_pullback_snd :
    imageRestrictHom g w ≫ pullback.snd g.imageι w = (pullback.snd g w).imageι :=
  IsClosedImmersion.lift_fac _ _ _

instance : IsIso (imageRestrictHom g w) :=
  IsClosedImmersion.isIso_lift _ _ (ker_imageι_pullback_snd g w).symm

/-- **The scheme-theoretic image of a base change along an open immersion is the base change of
the scheme-theoretic image.** For `g : T ⟶ Y` quasi-compact and `w : W ⟶ Y` an open immersion,

```
SIm_W(g ×_Y W)  ≅  SIm_Y(g) ×_Y W
```

as closed subschemes of `W`; the identification over `W` is
`AlgebraicGeometry.Scheme.imageRestrictIso_hom_pullback_snd`, and its compatibility with the
two factorizations is `AlgebraicGeometry.Scheme.toImage_imageRestrictIso_hom_pullback_fst`.

(blueprint: `lemma:nagata-scheme-image-restrict-open`) -/
noncomputable def imageRestrictIso :
    (pullback.snd g w).image ≅ pullback g.imageι w :=
  asIso (imageRestrictHom g w)

@[reassoc (attr := simp)]
lemma imageRestrictIso_hom_pullback_snd :
    (imageRestrictIso g w).hom ≫ pullback.snd g.imageι w = (pullback.snd g w).imageι :=
  imageRestrictHom_pullback_snd g w

/-- The identification of the two scheme-theoretic images lies over `Y`: composing it with the
projection to `SIm_Y(g)` and then with `i_g` is the same as including into `W` and then into
`Y`. -/
@[reassoc]
lemma imageRestrictIso_hom_pullback_fst_imageι :
    (imageRestrictIso g w).hom ≫ pullback.fst g.imageι w ≫ g.imageι =
      (pullback.snd g w).imageι ≫ w := by
  rw [pullback.condition, ← Category.assoc, imageRestrictIso_hom_pullback_snd]

/-- The identification of the two scheme-theoretic images is compatible with the two
factorizations: `g_W^{im}` followed by the projection to `SIm_Y(g)` is the projection to `T`
followed by `g^{im}`. -/
@[reassoc]
lemma toImage_imageRestrictIso_hom_pullback_fst :
    (pullback.snd g w).toImage ≫ (imageRestrictIso g w).hom ≫ pullback.fst g.imageι w =
      pullback.fst g w ≫ g.toImage := by
  rw [← cancel_mono g.imageι]
  simp only [Category.assoc, Hom.toImage_imageι]
  rw [imageRestrictIso_hom_pullback_fst_imageι, Hom.toImage_imageι_assoc]
  exact pullback.condition.symm

end RestrictOpen

end AlgebraicGeometry.Scheme
