## What changed

Restored `Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability` verbatim from
`quarantine/Sheaf/AlgebraicGeometry/EllAdicLocalizingBrownRepresentability.lean`, as requested
by its current rework entry. The module was absent from the library after the cluster restore.
The preserved source already proves both assigned declarations from the current interfaces.
No target, declaration signature, definition, instance, public import, or archive was changed.

The representability proof forms the additive Hom functor, supplies opposite triangulated
structures, transports coproduct preservation to product preservation, and applies
`ellAdic_localizing_cohomological_isRepresentable`. The second proof applies Mathlib's
partial-adjoint criterion to those representations. The universe of all discrete indexing
types remains u+1, including the empty indexing type. No compact-generation assumption or
cohomological bound on the field was introduced.

Validation: `lcompile.py` compiled the restored module with exit code 0 in 4.5 seconds,
without errors or warnings. LeanFinder, Loogle, and Mathlib/source searches confirmed the
partial-adjoint assembly API; no shorter geometric theorem replaces the two stated inputs.
The dependency signatures and the unit route were checked. Restoration retains the DAG's
existing Lean attachment and both proof dependencies, so the existing node needs no edits.

Change record: `coord/changes/F4-ell-adic-localizing-brown-restoration.md`.

## Proved and sorry left

The archived item has zero sorries; the restored item has zero sorries. Holes closed: 0.
Holes added: 0. No split-off statements or new nodes.

The restored complete proofs are
`AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_localizing_lowerStar_hom_isRepresentable`
and `AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_isLeftAdjoint_localizingLowerStar`.
These use the existing proper localizing pushforward and cohomological representability
interfaces; this delivery makes no claim to close their transitive proof obligations.

## No longer needed

None. No import, node, or module was pruned. Both stated proof dependencies remain used:
`lem-sfb-adic-proper-localizing-pushforward` and
`lem-sfb-adic-localizing-cohomological-representability`. The absent item and its quarantined
consumers are not withdrawn. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The assigned module is absent from `lean/` and is preserved at its rework quarantine path.
It is a zero-hole restoration, rather than a new proof of an unfinished theorem. Its archived
proof already compiles against the current restored dependency interfaces. No mathematical
error was found in the statements or DAG plan. The generic downstream tool cannot enumerate
consumers of a missing module, so both current and quarantined sources were searched directly.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
