/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A7
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackSingleCohomology

/-! # Pullback cohomology on a locus with one locally free cohomology sheaf

Compatibility import for the adopted source theorem
`AlgebraicGeometry.Scheme.Modules.nonempty_homology_derivedPullback_iso_of_locally_single`.
Its proof uses the flat single-cohomology open locus, termwise pullback of a flat single,
and derived pullback composition, as before.

Source: Stacks Project, Tag 0B9S and the perfect-locus cohomology-sheaf gluing argument
(blueprint: lem-pc-derived-pullback-single-cohomology).
-/

@[expose] public section
