## What changed

Restored `lean/Sheaf/AlgebraicGeometry/VectorIntegrationLocalTraceCompatibility.lean`
from the quarantine path recorded in `coord/rework.tsv`. Repaired elaboration in
the private `restricted_normalization` proof and its
application in `vectorIntegrationLocalSheafTrace_compatible_of_baseChange` by
making `ordinaryFiniteDegreeZero` and `ordinaryFiniteSingleFunctor` locally
`implicit_reducible`. These two wrappers expand to the existing canonical single-degree
embedding. The restriction formula uses the explicit embedding, while the unit
comparison uses the cached wrappers; local implicit reducibility lets rewriting recognize
that their endpoints coincide. The proof still applies the inverse Hom restriction
formula, the constant-unit composition equation, inverse-compositor cancellation,
and mapped-isomorphism cancellation, in that order.

All public declarations, definition bodies, public attributes, imports and signatures
are retained. The implicit reducibility attributes are local to this file; no shared
interface or consumer adaptation is needed.
The existing DAG proof and dependencies describe this same argument, so no node
changes or interface change records are needed.

Validation: the restored module compiled cleanly through `lcompile.py` in 33.6 s
(exit 0), with no errors or warnings. All Lean lines satisfy the 100-character limit.

## Proved and sorry left

This is a zero-hole compile repair: the archived item has 0 `sorry`s, and the
restored item has 0. Holes closed: none. Holes added: none. Split-off statements:
none. The existing proofs of
`AlgebraicGeometry.Etale.vectorIntegrationLocalSheafTrace_normalization_iff`,
`AlgebraicGeometry.Etale.vectorIntegrationLocalSheafTrace_compatible_of_baseChange`,
and `AlgebraicGeometry.Etale.vectorIntegrationLocalSheafTrace_compatible` are retained,
with their private normalization helper repaired. Their node is
`lem-amb-vector-integration-local-trace-compatibility`.

## No longer needed

None. No imports, declarations, nodes or modules are pruned. In particular the
quarantined item and its Lean attachment are restored, not withdrawn. Each private
proof import still supplies a theorem used by the existing argument.

## Where the brief, the DAG or earlier work was wrong

The recorded global build rejected `simp only` for making no progress. A fresh
compile also exposed the cause: expressions involving `ordinaryFiniteUnit` were
not type-correct at implicit transparency when compared to the explicit
single-functor image. The unit now expands through two cached wrappers. The local
implicit reducibility declarations restore the conversions needed by the existing proof
without changing its mathematical route. The assignment's generic discussion of
holes does not describe the current item: this rework has zero holes.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
