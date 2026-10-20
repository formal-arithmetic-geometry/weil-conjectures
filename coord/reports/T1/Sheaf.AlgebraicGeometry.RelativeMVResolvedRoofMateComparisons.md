## What changed

Restored `Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofMateComparisons` from the
complete quarantine archive listed in `coord/rework.tsv`. The archive contains
no holes. Against the current dependencies, the archived file and a minimal
restoration both exceed the unchanged 60-second single-file limit.

Removed the redundant local irreducibility entry for `derivedPullback`, which
upstream now declares with `irreducible_def`. Added local priority for
`schemeMVModuleAbelian`, kept `RingedSpace.moduleDirectImage` folded, and enabled
the backward definitional-equality API. The isolated global mate proof then
compiled in 22.1 seconds, compared with 56.3 seconds without those controls.
The public theorem respects these transparency boundaries. The final inverse
comparison uses explicit congruence; it never unfolds the unexposed `inv`
construction to compare its isomorphism witnesses.

Five proved private helpers keep the final proof operations abstract:
`map_first_roof_transport` applies the prescribed first-component equation;
`roof_denominator_first` computes the denominator component for abstract row functors;
`transport_roof_mate` applies naturality of the adjunction Hom equivalence;
`roof_denominator_transport` transports its inverse along the component equality;
`combine_mate_comparisons` assembles the global, middle and intersection data.
The first inverse is given its existing isomorphism proof explicitly. The body
reduces the statement aliases once with projection reduction disabled, avoiding
repeated comparisons through local row abbreviations.
The global-transpose heartbeat budget decreases from 800000 to 50000 and the
public theorem budget from 1000000 to 200000. The 60-second deadline is unchanged.

The public theorem statement and docstring and all five imports are textually
identical to the archive. The proof still uses
`relativeMV_normalized_coefficient_roof`, the conjugate-mate counit identity,
and `relativeMV_resolved_roof_open_mate_comparisons`. No data definition,
source-library declaration, target, hypothesis or conclusion changes.

The complete repaired proof compiled through `lcompile.py` in 39.3 seconds,
exit code 0, with no errors or warnings. The diagnostic copy has the identical
final code. Profiling options and traces are absent from the delivered file.
Delivery preflight recompiles the final file and checks its axioms. All Lean
lines are at most 100 characters.

Change record:
`coord/changes/T1-relative-mv-resolved-roof-mate-restoration.md`.
The sole archived direct consumer,
`Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofVertexNormalization`, applies the
identical public statement with the same arguments. No adaptation is needed.

## Proved and sorry left

Assigned zero-hole restoration and compilation repair. Holes closed: none (0 of 0).
Holes added: none. Split off: none. Sorries left: none.
`AlgebraicGeometry.relativeMV_resolved_roof_mate_comparisons` remains fully proved.
The three existing private mate helpers and all five new private helpers are
proved. No unproved intermediate statement or data construction is introduced.

## No longer needed

No import, module or DAG node is pruned. All five imports and the quarantined
parent's dependency are preserved. The redundant local irreducibility entry for
`derivedPullback` and repeated concrete transport elaboration are removed.

## Where the brief, the DAG or earlier work was wrong

The operative assignment is the zero-hole restoration in `coord/rework.tsv`,
whose original recorded failure was a cluster restore. There is no current
item-specific return in `coord/returns/T1.md`. Absence of the module from `lean/`
is not withdrawal; the complete archived proof is restored.

Searches of `dag/nodes` and `dag/units` by module, declaration and blueprint tag
find no attachment for `lem-pc-relative-mv-resolved-roof-mate-comparisons` in this
snapshot. Its archived blueprint tag and proof dependencies are preserved.
No public statement is added and no replacement DAG node is invented.

The required `msearch.py` searches ran. Loogle returned `conjugateEquiv` and its
API; LeanFinder returned generic mate/counit identities; grep located
`conjugateEquiv_counit` in Mathlib. Searches of both library roots found no
replacement for this specialized theorem. The existing argument already uses
that Mathlib identity. Zero object maps and empty, repeated or full opens need
no new assumptions: the repair only changes elaboration and generic equality
transport.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
