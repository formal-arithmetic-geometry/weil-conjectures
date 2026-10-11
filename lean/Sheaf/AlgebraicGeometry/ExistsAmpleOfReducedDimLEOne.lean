/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.Ample

/-! # Ample invertible modules on reduced Noetherian schemes of dimension at most one

Source: Stacks Project, Varieties, Lemma 09NX; Properties, Lemmas 0AAX and 0CKV
(blueprint: lem-sc-reduced-dim-le-one-ample).
-/

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A reduced Noetherian separated scheme of dimension at most one admits an ample
invertible module. The empty scheme is included.
Source: Stacks Project, Varieties, Lemma 09NX, with the dimension-zero branch from
Properties, Lemmas 0AAX and 0CKV (blueprint: lem-sc-reduced-dim-le-one-ample).

Proof:
1. If `X` is empty or has dimension at most zero, `lem-sc-zero-dim-noetherian-affine`
makes it affine, and its structure sheaf is ample. Otherwise its dimension is one.
2. Its finitely many reduced irreducible components are integral, Noetherian, separated,
and of dimension zero or one. Choose ample modules on them using
`lem-sc-integral-dim-one-ample` and `lem-sc-zero-dim-noetherian-affine`. Their pairwise
intersections form a finite set `T` of closed points, and each point outside `T` lies on
one component, by `lem-sc-component-intersections-finite` (and `def-pc-integral-scheme`).
3. Use `lem-sc-ample-finite-principal-affine` to replace each component module by a
positive power with a section whose affine nonvanishing locus contains its part of `T`.
The pairwise intersections are finite discrete spaces, so
`lem-sc-glue-component-line-bundles` glues the modules and sections to a module `L`
and section `s` on `X`.
4. The open `X_s` contains `T` and is covered by the affine closed subschemes given by
the component sections. It is affine by `lem-sc-closed-affine-union-affine`.
5. For `x` outside `T`, let `Z₁` be its unique component and let `I` be the ideal of the
reduced union of the other components. Its image `I₁` on `Z₁` does not vanish at `x`.
Use `lem-sc-ample-ideal-section` to obtain a section `t₁` of `I₁ L₁^m₁` nonvanishing
at `x`, and the definition `def-weil-pbc-ample-invertible-module` to obtain a section
`t₂` of `L₁^m₂` with affine nonvanishing locus containing `x`.
6. Their product `t` belongs to `I₁ L₁^(m₁+m₂)` and its nonvanishing locus contains `x`.
It is affine by `lem-sc-affine-cap-section-open`, applied inside the affine locus of `t₂`.
7. By `lem-sc-conductor-sections`, extend `t` to a section of `L^(m₁+m₂)` vanishing on
all other components. Its nonvanishing locus is the affine locus from step 6.
Together with `X_s` from step 4, these sections satisfy the absolute ampleness criterion
`def-weil-pbc-ample-invertible-module` at every point; `X` is already quasi-compact.
-/
theorem exists_isAmple_of_reduced_dim_le_one (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X] [IsReduced X] [X.IsSeparated]
    (hdim : topologicalKrullDim X ≤ 1) :
    ∃ L : X.Modules, ∃ hL : L.IsInvertible, @IsAmple X L hL := by
  sorry

end AlgebraicGeometry.Scheme.Modules
