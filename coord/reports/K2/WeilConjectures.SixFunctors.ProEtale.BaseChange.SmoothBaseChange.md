## What changed

Restored AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap from the preferred
proof at 438e3d04508, adapted to the current upstream text. Its exact public statement,
all five comparison definitions, all existing public imports and the smooth-base-change
assembly are unchanged. The generic comparison_mate_transport is a fully proved private
helper; the source adds private imports of ComparisonCounitCore and ComparisonSquareCore.

The 2026-10-20 sync moved the five comparison definitions back upstream. The old counit
and square modules consequently import this item, so importing them back would create
a cycle. Reuse their existing proved arguments through lower Core interfaces in namespace
AlgebraicGeometry.ProEtale.ComparisonCore. Their statements expand the fixed upstream
comparison constants to their exact defining expressions: no new comparison definition,
choice or hypothesis is introduced. The original helper modules retain their exact public
interfaces and imports. Each lower Core carries the corresponding existing node; no
mathematical node is introduced. The counit proof supplies explicit adjunction arguments
to its formerly unconstrained rewrite, preventing an expensive typeclass search.

The ordinary path constructions did not use the moved comparisons. Relocated them
verbatim to ComparisonSquarePathsCore. The original ComparisonSquarePaths keeps both
public imports and publicly re-exports the core, preserving every original path name,
type and defining term. The existing path node records its new lower attachment.
The transport node records the recovered mate argument. The current blueprint and the
restored theorem allow arbitrary commutative rings; no finiteness condition is added.

Change record: coord/changes/K2-smooth-base-change-proof-restoration.md.
The source restoration needs its private helper and Sheaf proof imports registered for
future upstream syncs. Please add the maintainer-owned upstream exception row; this
worker has not edited coord/upstream-statement-exceptions.tsv.

Validation: all eight delivered modules compile through lcompile.py, including the
complete upstream exchange proof (49.2 seconds). The original comparison-definition
bodies and public theorem signatures were compared textually and are unchanged. The
path declarations in the lower module are verbatim. All delivered proofs have zero
sorry tokens. All five unchanged original helper consumers compiled successfully against the repaired
wrapper and were removed from the packet after checking. deliver3.py supplies the
final compile and axiom probes.

## Proved and sorry left

Closed 1 of 1 original holes:
AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap
(lem-weil-pbc-transport-identifies-exchange).
Added 0 holes; split off 0 holes. No sorry remains in the item or any delivered module.
All lower-interface theorems and all private helpers are fully proved. The existing
smooth-base-change assembly continues to use the same public transport theorem.

The lower interfaces reuse the already proved counit, two path normalizations,
component-to-derived-square transport and square-coherence arguments. Their existing
nodes now point to the lower interfaces. This is an import-cycle repair and restoration,
not a decomposition or a claim to have closed those pre-existing proofs again.

## No longer needed

No original public import is removed; no module or declaration is withdrawn.
ComparisonCounit and ComparisonSquare cannot be imported by the upstream proof after
the sync because they reach the item. Their original modules remain available and
needed by their consumers. The lower versions of those same proved arguments are
used instead. ComparisonSquarePaths no longer defines its declarations locally:
it re-exports the identical declarations from the core and retains its original public
imports. No mathematical dependency is pruned. Pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The preferred proof cannot simply recover its old imports: those imports became cyclic
after the five definitions returned upstream. The lower formula interfaces resolve that
cycle while retaining every upstream statement and definition. Copying all proofs into
the source was checked and compiled, but aggressively unfolding the comparison formulas
left poor compile margin. Reusing the existing helper arguments through lower interfaces
keeps the original modular proof and preserves the source-library boundary. Profiling
identified an unconstrained derived-mate rewrite; explicit adjunction arguments repair
that search without raising the per-file limit. No statement is disputed and the unit
route is unchanged. No new nodes are introduced.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
