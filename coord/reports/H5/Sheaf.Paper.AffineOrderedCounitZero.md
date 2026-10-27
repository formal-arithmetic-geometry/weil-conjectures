## What changed

Filled `AlgebraicGeometry.ProEtale.AffineOrderedIntegration.ordinary_counit_zero` in
`Sheaf.Paper.AffineOrderedCounitZero`, retaining its signature and public imports.
The added proof imports are `Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization`,
`Sheaf.Paper.AffineOrderedCounitDescentComparison`,
and `import all Sheaf.Paper.IteratedIntegration` (its proved projection-naturality
helper). The proof specializes the existing ordinary affine counit tensor normalization to
rank zero and transports its coefficient isomorphism to the ordered one. Private
proved helpers establish identity compact-support compatibility, source transport using
the existing `normalized_source_descent`, and naturality of the actual canonical projection map. The node records this route.
The proof-context record is `coord/changes/H5-affine-ordered-counit-zero-proof-context.md`.
The generic affine normalization and the proved projection-naturality helper in
`lem-pur-iterated-integration` are used as tools for the unit's existing ordered
integration step; the unit route is unchanged. The latter helper is a direct
pasting of naturality for the canonical projection's four factors.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.AffineOrderedIntegration.ordinary_counit_zero`
(node `lem-pur-affine-ordered-counit-zero`), 1 of 1 original holes.
No holes remain in this module and no holes are added or split off.
The proof uses existing library declarations, including their stated dependencies;
it does not claim to close their remaining admissions.

## No longer needed

No original imports are removed and no modules are withdrawn. The original direct
proof dependency `def-pur-affine-space-comparison` is replaced by reuse of the generic
normalization and explicit coefficient transport; its definitions remain available
through the unchanged statement imports. No claim is made that the underlying
module or node is globally unused. The other original dependencies remain used.

## Where the brief, the DAG or earlier work was wrong

The planned identity argument is valid, but the library already contains the
stronger `ordinaryAffineCounit_tensor_normalization` and the proved comparison
`normalized_source_descent`. Specialization and coefficient transport
avoid separately developing all identity projection/unitor coherence. No
statement or definition repair was necessary. The zero ring and empty base require
no extra hypothesis: the argument uses only functoriality and invertible comparisons.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
