/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Two constructions of compactifications

Both constructions in this file compactify by replacing the target of an immersion by its
scheme-theoretic image, which is a closed subscheme and hence proper over the old target.

- `AlgebraicGeometry.Compactification.ofImmersion`: if `f` factors as a quasi-compact
  immersion `g : X ⟶ P` followed by a proper `p : P ⟶ Y`, then `SIm_P(g)` compactifies `f`.
  This is the blueprint's `def:nagata-immersion-compactification` and
  `lemma:nagata-immersion-into-proper`; `AlgebraicGeometry.HasCompactification.of_isImmersion`
  is the unbundled form that downstream code consumes.
- `AlgebraicGeometry.Compactification.dense`: every compactification `c` with `c.i`
  quasi-compact refines to one whose open immersion is scheme-theoretically dominant, by
  replacing `c.Z` with the scheme-theoretic image of `c.i`. This is the blueprint's
  `def:nagata-dense-refinement` and `prop:nagata-dense-refinement`.

In both cases the two properties required of a compactification are already instances:

- `AlgebraicGeometry.IsImmersion.instIsOpenImmersionToImageOfQuasiCompact` (Stacks 01RG) makes
  the map to the scheme-theoretic image of a quasi-compact immersion an open immersion; note
  that an open immersion is in particular an immersion, so this applies to `c.i` as well.
- `f.imageι` is a closed immersion for *any* `f`, hence finite, hence proper, and properness
  is stable under composition.

The density of the refinement is `AlgebraicGeometry.Scheme.Hom.ker_toImage`, in the mirror
tree; it is the only part of either construction that is not already in Mathlib.

## Note on quasi-compactness

The `AlgebraicGeometry.Compactification` structure does not require `c.i` to be quasi-compact,
while the blueprint's notion of compactification does. Both constructions here need it and
take it as an instance argument;
`AlgebraicGeometry.Compactification.quasiCompact_openImmersion_iff` converts it to and from
quasi-compactness of the compactified morphism.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

namespace Compactification

/-- **A quasi-compact immersion into something proper compactifies.** If `f = g ≫ p` with
`g` a quasi-compact immersion and `p` proper, then the scheme-theoretic image of `g` is a
compactification of `f`: the map into it is an open immersion by Stacks 01RG, and it is
proper over `Y` because it is a closed subscheme of `P`.
(blueprint: `def:nagata-immersion-compactification`, `lemma:nagata-immersion-into-proper`) -/
noncomputable def ofImmersion {P : Scheme.{u}} {f : X ⟶ Y} (g : X ⟶ P) (p : P ⟶ Y)
    [IsImmersion g] [QuasiCompact g] [IsProper p] (hf : f = g ≫ p) : Compactification f where
  Z := g.image
  g := g.imageι ≫ p
  i := g.toImage
  comm := by rw [hf, ← Category.assoc, Scheme.Hom.toImage_imageι]
  isProper := inferInstance
  isOpenImmersion := inferInstance

@[simp]
lemma ofImmersion_Z {P : Scheme.{u}} {f : X ⟶ Y} (g : X ⟶ P) (p : P ⟶ Y)
    [IsImmersion g] [QuasiCompact g] [IsProper p] (hf : f = g ≫ p) :
    (ofImmersion g p hf).Z = g.image := rfl

@[simp]
lemma ofImmersion_g {P : Scheme.{u}} {f : X ⟶ Y} (g : X ⟶ P) (p : P ⟶ Y)
    [IsImmersion g] [QuasiCompact g] [IsProper p] (hf : f = g ≫ p) :
    (ofImmersion g p hf).g = g.imageι ≫ p := rfl

@[simp]
lemma ofImmersion_i {P : Scheme.{u}} {f : X ⟶ Y} (g : X ⟶ P) (p : P ⟶ Y)
    [IsImmersion g] [QuasiCompact g] [IsProper p] (hf : f = g ≫ p) :
    (ofImmersion g p hf).i = g.toImage := rfl

variable {f : X ⟶ Y} (c : Compactification f) [QuasiCompact c.i]

/-- **The dense refinement of a compactification.** Replacing `c.Z` by the scheme-theoretic
image of `c.i` gives a compactification of the same morphism whose open immersion is
scheme-theoretically dominant, by
`AlgebraicGeometry.Compactification.isSchemeTheoreticallyDominant_dense_i` below.
(blueprint: `def:nagata-dense-refinement`) -/
noncomputable def dense : Compactification f where
  Z := c.i.image
  g := c.i.imageι ≫ c.g
  i := c.i.toImage
  comm := by rw [← Category.assoc, Scheme.Hom.toImage_imageι]; exact c.comm
  isProper := inferInstance
  isOpenImmersion := inferInstance

@[simp] lemma dense_Z : c.dense.Z = c.i.image := rfl

@[simp] lemma dense_g : c.dense.g = c.i.imageι ≫ c.g := rfl

@[simp] lemma dense_i : c.dense.i = c.i.toImage := rfl

/-- **The dense refinement is scheme-theoretically dense**, which is the whole point of it.
(blueprint: `prop:nagata-dense-refinement`) -/
instance isSchemeTheoreticallyDominant_dense_i :
    IsSchemeTheoreticallyDominant c.dense.i :=
  inferInstanceAs (IsSchemeTheoreticallyDominant c.i.toImage)

/-- The open immersion of the dense refinement is again quasi-compact, so the refinement can
be refined again — idempotently, since it is already dense. -/
instance quasiCompact_dense_i : QuasiCompact c.dense.i :=
  inferInstanceAs (QuasiCompact c.i.toImage)

end Compactification

/-- A morphism that factors as a quasi-compact immersion followed by a proper morphism has a
compactification. This is the form in which
`AlgebraicGeometry.Compactification.ofImmersion` is meant to be used.
(blueprint: `lemma:nagata-immersion-into-proper`) -/
lemma HasCompactification.of_isImmersion {P : Scheme.{u}} {f : X ⟶ Y} (g : X ⟶ P) (p : P ⟶ Y)
    [IsImmersion g] [QuasiCompact g] [IsProper p] (hf : f = g ≫ p) : HasCompactification f :=
  (Compactification.ofImmersion g p hf).hasCompactification

end AlgebraicGeometry
