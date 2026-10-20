/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension

/-!
# Bounded projective resolutions and projective dimension

The comparison between explicit bounded projective resolutions and Mathlib's projective
dimension is proved in the adopted source module, which this module reexports. Reusing that
module also keeps the bounded-resolution predicate and the splicing construction on the same
`WeilConjectures.RingTheory.GlobalDimension` definitions.

Source: Stacks Project, Algebra, Lemma 065R.
(blueprint: lem-weil-pbc-projective-resolution-ext-degree).
-/

@[expose] public section
