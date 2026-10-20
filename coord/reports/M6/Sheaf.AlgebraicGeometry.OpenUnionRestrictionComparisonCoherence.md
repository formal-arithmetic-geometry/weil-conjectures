## What changed

Retired the duplicate module
`Sheaf.AlgebraicGeometry.OpenUnionRestrictionComparisonCoherence`, which is listed
in `coord/retire-items.tsv`, in favor of the proved source module
`WeilConjectures.AlgebraicGeometry.OpenUnionRestrictionComparisonCoherence`.
The sole consumer, `Sheaf.AlgebraicGeometry.OpenUnionRestrictionComparisonDiagram`,
changes only its private proof import. Its theorem signature and proof are unchanged.
The coherence node's Lean attachment now points to the existing source theorem;
its mathematical statement, proof and dependencies remain intact.

Change record:
`coord/changes/retire-open-union-restriction-comparison-coherence.md`.

Validation: the original item compiled cleanly. A separate scratch theorem with
the item's verbatim original signature compiles by directly applying the source
theorem, despite the original's two unused let bindings JW and JV. Both the
scratch theorem and the source theorem print exactly propext, Classical.choice,
and Quot.sound as axioms. The migrated consumer compiles without warnings. The
import-direction check permits the replacement source import.

## Proved and sorry left

The item has zero holes before retirement and zero afterward. Holes closed: none
(0 of 0). Holes added: none. Statements split off: none. No sorry remains in the
delivered consumer. The complete source proof of
`AlgebraicGeometry.Scheme.open_union_restriction_comparison_coherence` is reused,
with the original statement checked by Lean; this retirement is not counted as
new proof progress.

## No longer needed

Pruned duplicate module:
`Sheaf.AlgebraicGeometry.OpenUnionRestrictionComparisonCoherence`.
The consumer removes that private proof import and imports the source module
instead. The duplicate private helper `cancel_mapped_iso_pasting` also disappears;
its source counterpart remains proved and unchanged.

No mathematical node or proof dependency is pruned. In particular,
`lem-sc-open-union-restriction-comparison-coherence` remains needed by
`lem-sc-open-union-restriction-comparison-diagram`, and is retained with its source
Lean attachment. Restriction maps and isomorphism descent are still needed by the
source proof. Searches checked current Lean importers, quarantined Lean modules,
DAG parent dependencies and the unit's realized route. There is no replacement of
a required mathematical step by an empty module: the required theorem is supplied
by its existing complete source proof.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an unfinished chain, but the current item has
already been fully proved. The retirement inventory records the Sheaf and source
copies as DIFFERENT because of their former dependency closures. In the current
sources both copies have exactly the same two imports, from WeilConjectures.
Their only signature difference consists of the unused JW and JV let bindings;
the direct original-signature application verifies definitional compatibility.
No statement repair, definition change or additional intermediate theorem is
necessary. Empty, repeated and disjoint opens retain exactly the original type.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
