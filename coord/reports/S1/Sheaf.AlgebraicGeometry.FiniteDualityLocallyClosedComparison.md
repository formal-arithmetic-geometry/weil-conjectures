## What changed

Proved `AlgebraicGeometry.ProEtale.locallyClosed_comparison_factorization` with its
original signature. A proved private lemma, `normalizedComparison_unique`, performs
the cancellation argument in arbitrary categories. The specialization identifies the
closure exceptional functors using equality of the composite scheme morphisms and
proof irrelevance for their instance arguments. It then constructs the two comparisons
through their common normalized values. Postcomposition with the second transport and
the two `unit_normalization` equations proves the gamma square. The normalization
conditions determine both isomorphisms uniquely by cancellation.

Only the item module and its existing node are changed. No public signature,
definition, visibility or import is changed. The node's last proof step now records
the actual elementary argument; its earlier existence-proof steps are retained.

Validation: the complete item module compiled successfully through `lcompile.py`
(exit code 0, 21.5 seconds). The delivery checker performs the required packet checks.

## Proved and sorry left

Closed one of the two original holes:
`AlgebraicGeometry.ProEtale.locallyClosed_comparison_factorization`.
Added zero holes and split off zero statements. The private lemma is fully proved.

One existing hole remains, unchanged:
`AlgebraicGeometry.ProEtale.finiteDuality_locallyClosed_comparison`, attached to
`lem-weil-finite-duality-locally-closed-comparison`. Its original complete proof plan
and source remain in its docstring and node. This delivery is a partial proof of a
module with multiple holes, not a decomposition of the existence theorem.

## No longer needed

No imports, declarations, or modules are removed: the unchanged existence theorem and the public
definitions still retain their interfaces and planned dependencies. For the
factorization theorem itself no new conjugation, counit-transpose, closure-square,
or relative-transpose theorem is needed. Its actual conclusion follows solely from
the supplied comparison-unit normalizations and equality of composite morphisms.

The final DAG step therefore has no proof dependencies. The top-level
`def-weil-pbc-adjunction-conjugate` and `lem-cat-right-adjoint-composition` proof-dependency
edges are removed because only that old final step cited them. Their declarations
remain in the library and the existing adjunction definitions remain unchanged.
All dependencies of the retained existence-proof steps stay in the node.

## Where the brief, the DAG or earlier work was wrong

The earlier final proof step was substantially longer than the Lean statement
requires: its two `HEq` normalization clauses already specify the comparison
isomorphisms uniquely, and `unit_normalization` directly implies the gamma square.
No hypotheses or conclusions were weakened. The generic proof also covers identity,
empty schemes, and repeated factorizations: only invertibility and the supplied
normalization equations are used.

The extracted existence interfaces use different coefficient presentations: the
closure-realization interface uses a smaller-universe extension with a lifted
coefficient quotient; the relative-transpose interface uses `PurityFiniteSetting`.
The assigned existence statement instead quantifies over an arbitrary extension
in the coefficient-value universe. This requires explicit transport or a direct
assembly from the closed comparison; this delivery does not assert that those
interfaces apply definitionally. No downstream definition or statement was changed.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
