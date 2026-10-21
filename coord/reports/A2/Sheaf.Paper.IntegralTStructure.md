## What changed

Restored `lean/Sheaf/Paper/IntegralTStructure.lean` from the exact quarantine source
recorded in `coord/rework.tsv` (row for `Sheaf.Paper.IntegralTStructure`, quarantine
baseline `5f7b33eac`). The module had been removed by the merge queue after a cluster
restore. Its archived proof already compiles against the current dependencies, so
all declarations, public imports, definition bodies and proofs are preserved.
The existing DAG attachment and proof dependencies remain valid and unchanged.

The restored declarations give the inherited triangulation, induced standard
t-structure, linear shifts, boundedness, heart description, canonical ambient
truncation comparisons, and preservation of the same uniformizer-torsion exponent.
The conditional tower calculation stays in the publicly imported
`Sheaf.Paper.IntegralCanonicalTruncations` with its Tor hypothesis unchanged.

Validation: `lcompile.py` compiled the restored module cleanly (10.2 seconds,
exit code 0). Read the existing dependency signatures and the Mathlib induced
t-structure and truncation adjunction lemmas against the archived argument.
Logged fresh `msearch.py` searches: Loogle
`CategoryTheory.ObjectProperty.tStructure_isLE_iff` (one exact generic hit),
LeanFinder for a full triangulated subcategory stable under truncation (eight
generic hits), and grep for `HasInducedTStructure|to_truncLE_obj_ext|from_truncGE_obj_ext`
(eleven hits). The archive already uses these generic results directly;
no shorter replacement or additional lemma was needed.

## Proved and sorry left

Restoration item: the quarantined module contains zero holes; zero holes closed,
zero holes added, zero holes remaining, and zero statements split off.
All four named theorem proofs are complete:

- `AlgebraicGeometry.Scheme.pbcIntegralProperty_isTriangulated`;
- `AlgebraicGeometry.Scheme.pbcIntegralProperty_hasInducedTStructure`;
- `AlgebraicGeometry.Scheme.pbcIntegralShift_isLinear`;
- `AlgebraicGeometry.Scheme.pbc_integral_tstructure`.

`AlgebraicGeometry.Scheme.pbcIntegralTStructure` remains the actual Mathlib induced
construction. No definition contains `sorry`. Existing dependencies remain the
same; this report makes no claim that all their transitive proofs are closed.

## No longer needed

None. No import, declaration, node or module is withdrawn. In particular the
quarantined parent `Sheaf.Paper.LocalizedTStructure` still uses this module's
public declarations; zero current Lean importers does not authorize pruning it.

## Where the brief, the DAG or earlier work was wrong

The generic brief says the item contains a hole or has a repair. This item is the
explicit quarantined restoration listed in `coord/rework.tsv`: its archived proof
has zero holes and already compiles. Its absence was not a mathematical withdrawal.
Restoring the module repairs that absence; no statement or definition repair was
needed, and neither a replacement empty module nor a deletion was used.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
