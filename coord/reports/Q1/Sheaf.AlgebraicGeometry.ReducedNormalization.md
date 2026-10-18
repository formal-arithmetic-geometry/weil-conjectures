## What changed

Proved `AlgebraicGeometry.Scheme.isIntegral_reducedNormalizationComponent` in
`lean/Sheaf/AlgebraicGeometry/ReducedNormalization.lean`. Added the proof-only import
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`, whose proved instance
`AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal` supplies
reducedness. The underlying topological space is definitionally the component subtype;
`Subtype.irreducibleSpace Z.2.1` supplies its irreducibility. Mathlib's
`AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced` combines these properties.
The proof implements the existing declaration docstring's argument. No definition,
statement, visibility, or DAG route was changed.

Validation: the complete module compiles through `lcompile.py` without errors or warnings.
The import-direction check permits the new proof import. An empty ambient scheme has no
irreducible-component indices, so the statement requires no nonemptiness hypothesis on X;
each actual component is nonempty by its irreducibility. No Noetherian or finiteness
hypothesis is used.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.isIntegral_reducedNormalizationComponent`
(blueprint: `def-weil-pbc-reduced-normalization`).

Added 0 holes; split off 0 statements. No sorry remains in the delivered module.

## No longer needed

None. No proof dependencies were declared in the node, and the existing public imports
support the unchanged component, normalization, and coproduct constructions. The added
proof import is used for reducedness. No nodes or modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

None. The definition node has no numbered proof plan; its integral-component theorem's
existing docstring gives the argument followed here. Existing library and Mathlib results
suffice to close it directly. The blueprint unit's route is preserved.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
