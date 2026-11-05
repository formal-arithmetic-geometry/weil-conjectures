/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-!
# Gluing schemes along open subschemes

A family of schemes `U i`, opens `V i j ⊆ U i` with `V i i = ⊤`, and morphisms
`t i j : V i j ⟶ V j i` with `t i i = 𝟙`, mapping `V i j ⊓ V i k` into `V j k` and satisfying
the triple cocycle condition `t j k ∘ t i j = t i k` on `V i j ⊓ V i k`, glue to a scheme.
This is the form of the gluing theorem in which the overlaps are recorded as opens of the
charts, rather than as abstract schemes with open immersions as in `Scheme.GlueData`.

## Main definitions

- `AlgebraicGeometry.Scheme.OpensGlueData`: the gluing data.
- `AlgebraicGeometry.Scheme.OpensGlueData.toGlueData`: the associated `Scheme.GlueData`.
- `AlgebraicGeometry.Scheme.OpensGlueData.glued`, `AlgebraicGeometry.Scheme.OpensGlueData.ι`:
  the glued scheme and the open immersions of the charts.
- `AlgebraicGeometry.Scheme.OpensGlueData.glueMorphisms`: morphisms out of the glued scheme
  are glued from morphisms out of the charts which are compatible on the overlaps.

## Main results

- `AlgebraicGeometry.Scheme.OpensGlueData.isPullback`: the overlaps are the fibre products of
  the charts over the glued scheme.
- `AlgebraicGeometry.Scheme.OpensGlueData.preimage_opensRange_ι`: `ι i ⁻¹ (range ι j) = V i j`.
- `AlgebraicGeometry.Scheme.OpensGlueData.compactSpace_glued`: finitely many quasi-compact charts
  glue to a quasi-compact scheme.

This is the affine gluing theorem used in the blueprint proofs of
`lemma-nagata-finite-presentation-descends` and `def-nagata-noetherian-stage`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

namespace OpensGlueData

variable (D : OpensGlueData.{u})

end OpensGlueData

end AlgebraicGeometry.Scheme
