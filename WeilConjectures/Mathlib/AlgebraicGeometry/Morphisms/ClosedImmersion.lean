/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The universal property of the scheme-theoretic image

For a morphism `g : T ⟶ Y`, Mathlib provides the scheme-theoretic image `g.image`
together with the closed immersion `g.imageι : g.image ⟶ Y`, the factor map
`g.toImage : T ⟶ g.image` and the factorization `g.toImage_imageι`
(blueprint labels `def:nagata-scheme-theoretic-image`,
`lemma:nagata-scheme-image-ideal-qc` and `def:nagata-scheme-image-factor`).

We record the universal property of the scheme-theoretic image among factorizations of
`g` through closed immersions:

- `AlgebraicGeometry.Scheme.Hom.image.lift`: given a factorization `g = h ≫ z` with
  `z : Z ⟶ Y` a closed immersion, the canonical map `g.image ⟶ Z`
  (`def:nagata-scheme-image-comparison`);
- `AlgebraicGeometry.Scheme.Hom.image.lift_fac`,
  `AlgebraicGeometry.Scheme.Hom.image.lift_unique`: `image.lift` is the unique morphism
  compatible with the inclusions into `Y` (`lemma:nagata-scheme-image-universal`);
- `AlgebraicGeometry.Scheme.Hom.le_ker_iff_exists_fac`: the scheme-theoretic image is
  the smallest closed subscheme of `Y` through which `g` factors.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {T Y Z : Scheme.{u}}

namespace Scheme.Hom.image

/-- Given a factorization `g = h ≫ z` with `z : Z ⟶ Y` a closed immersion, the
canonical comparison map from the scheme-theoretic image of `g` to `Z`.
(Blueprint: `def:nagata-scheme-image-comparison`.) -/
def lift (g : T ⟶ Y) (h : T ⟶ Z) (z : Z ⟶ Y) [IsClosedImmersion z]
    (w : h ≫ z = g) : g.image ⟶ Z :=
  IsClosedImmersion.lift z g.imageι (by simpa using w ▸ Scheme.Hom.le_ker_comp h z)

@[reassoc (attr := simp)]
lemma lift_fac (g : T ⟶ Y) (h : T ⟶ Z) (z : Z ⟶ Y) [IsClosedImmersion z]
    (w : h ≫ z = g) : lift g h z w ≫ z = g.imageι :=
  IsClosedImmersion.lift_fac _ _ _

/-- The comparison map from the scheme-theoretic image to a closed factorization is a
closed immersion. -/
lemma isClosedImmersion_lift (g : T ⟶ Y) (h : T ⟶ Z) (z : Z ⟶ Y)
    [IsClosedImmersion z] (w : h ≫ z = g) :
    IsClosedImmersion (lift g h z w) :=
  have : IsClosedImmersion (lift g h z w ≫ z) := by
    rw [lift_fac]
    infer_instance
  IsClosedImmersion.of_comp_isClosedImmersion _ z

/-- Universal property of the scheme-theoretic image: `image.lift` is the unique
morphism from the scheme-theoretic image which is compatible with the maps to the
common target. (Blueprint: `lemma:nagata-scheme-image-universal`.) -/
lemma lift_unique (g : T ⟶ Y) (h : T ⟶ Z) (z : Z ⟶ Y) [IsClosedImmersion z]
    (w : h ≫ z = g) (c : g.image ⟶ Z) (hc : c ≫ z = g.imageι) :
    c = lift g h z w := by
  rw [← cancel_mono z, hc, lift_fac]

end Scheme.Hom.image

/-- The scheme-theoretic image is the smallest closed subscheme of `Y` through which
`g` factors: a closed subscheme `z : Z ⟶ Y` contains the scheme-theoretic image of `g`
(i.e. `z.ker ≤ g.ker`) if and only if `g` factors through `z`. -/
theorem Scheme.Hom.le_ker_iff_exists_fac (g : T ⟶ Y) (z : Z ⟶ Y) [IsClosedImmersion z] :
    z.ker ≤ g.ker ↔ ∃ h : T ⟶ Z, h ≫ z = g := by
  refine ⟨fun H ↦ ⟨g.toImage ≫ IsClosedImmersion.lift z g.imageι (by simpa using H), ?_⟩,
    fun ⟨h, w⟩ ↦ w ▸ Scheme.Hom.le_ker_comp h z⟩
  rw [Category.assoc, IsClosedImmersion.lift_fac, Scheme.Hom.toImage_imageι]

end AlgebraicGeometry
