## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.fibreProduct_atlas_tests` in
`Sheaf.AlgebraicGeometry.FibreProductAtlasTests`, preserving its signature and
`fibreProductAtlasMap` verbatim. Added three fully proved private helpers:
`property_of_test` transfers a scheme property between representing squares by
Yoneda full faithfulness; `diagonal_square` constructs the diagonal pullback;
`test_square` constructs the arbitrary scheme test by pullback universal properties.
The resulting canonical isomorphisms satisfy all three required projection equations.
Étaleness and surjectivity follow from Mathlib's base-change and composition
instances, exactly the singleton covering cases of the stated dependencies.

Added the proof import
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts`.
Updated the existing node's proof and proof dependencies to match the Lean argument.
No statements, definitions, public imports or consumers changed.

Validation: the single module compiles through `lcompile.py` without warnings
(18.3 seconds). The delivery preflight checks axioms for every declaration.
Read Stacks `spaces.tex`, Tag 04T9, last paragraph, against the implementation.
The argument works without nonemptiness, separation, or quasi-compactness assumptions:
empty schemes and identity atlases use the same universal properties.

## Proved and sorry left

Closed 1 hole:
`AlgebraicGeometry.AlgebraicSpace.fibreProduct_atlas_tests`
(node `lem-trf-fibre-product-atlas-tests`).
Added 0 holes; split off 0 statements. The delivered module has 0 `sorry`.
Every helper is fully proved from Mathlib and the supplied hypotheses.

## No longer needed

Removed the proof import `Mathlib.AlgebraicGeometry.Sites.MorphismProperty`:
the singleton permanence argument uses the scheme morphism-property instances
directly, rather than invoking the covering precoverage interface.
The node's proof no longer cites `def-weil-pbc-sites-and-cohomology`:
the Lean theorem does not assert the sheaf condition of the presheaf pullback,
so the separate componentwise sheaf-gluing argument is unnecessary here.
The site definitions remain available through the unchanged public imports.
All other declared proof dependencies are retained; no module is withdrawn and
no whole-module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The old first proof step proved that the presheaf pullback is a sheaf, although
this is not a conjunct of this Lean theorem. The node now starts with the diagonal
test actually used by the statement. This removes no unit-level step:
`sk-i-curve-zero` has no realization attached to this lower-level atlas lemma.
No mathematical statement or definition repair was necessary.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
