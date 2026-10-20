/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.StalkComparisonPullbackNaturality
public import Sheaf.Algebra.Homology.KFlat

/-! # Naturality of the localized comparison into derived pullback

Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8.
(blueprint: lem-pc-stalk-comparison-pullback-naturality).

Re-export the adopted source implementation at the historical module path. The
comparison map and its naturality theorem then have one implementation, so this
module can be imported together with the source module. The K-flat import retains
the original predicate spelling; its defining acyclic-test-complex formula is
identical to the source predicate `CochainComplex.IsKFlatTensor`.
-/

@[expose] public section
