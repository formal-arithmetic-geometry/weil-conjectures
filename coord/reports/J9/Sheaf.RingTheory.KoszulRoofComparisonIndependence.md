## What changed

Retired Sheaf.RingTheory.KoszulRoofComparisonIndependence in favor of the existing,
fully proved WeilConjectures.RingTheory.KoszulRoofComparisonIndependence. The source
result has exactly the required conclusion and omits only the unused regularity
hypothesis on the second sequence. The sole direct consumer,
Sheaf.RingTheory.KoszulRegularSequenceDualComplex, now imports the source module and
omits the corresponding hreg argument in intrinsic_ext_determinant_roof. Every surviving
consumer signature, all definitions, and the source tree stay unchanged.

The node lem-sc-koszul-roof-comparison-independence now records the source module and
its actual signature. Its mathematical statement, three proof steps and proof dependencies
are preserved. The parent node lem-sc-koszul-ext-determinant-roof still uses it.

Change record: coord/changes/J9-koszul-roof-upstream-retirement.md.

## Proved and sorry left

The assigned module started with zero sorry holes. Closed: none (0 of 0). Added: none.
Remaining in the delivered Lean files: none. Split off: none.

ExteriorAlgebra.koszul_roof_comparison_independent is already proved in the source
library, with only propext, Classical.choice and Quot.sound. A sandbox test proves the
entire former signature by applying it, including the formerly required hregg hypothesis.
This delivery is duplicate retirement, not new proof progress or decomposition.

## No longer needed

Pruned module: Sheaf.RingTheory.KoszulRoofComparisonIndependence.
Removed proof import in Sheaf.RingTheory.KoszulRegularSequenceDualComplex:
Sheaf.RingTheory.KoszulRoofComparisonIndependence; replaced by the source module.
Removed duplicate private helpers pairingDual_injective_of_basis, conormalVector_comp,
and conormalVector_surjective together with the duplicate public theorem body; the source
module retains all four complete proofs. No mathematical nodes or declared proof
dependencies are pruned: generator substitution, derived top evaluation, conormal basis
and determinant pairing remain used by the source proof. No unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief says this item contains sorry or has a repair. Its actual assignment
is the zero-hole retirement row in coord/retire-items.tsv. The earlier DIFFERENT/kept entry
correctly noticed a signature difference but did not migrate the consumer. That difference
is solely the unused second regularity argument, so it does not prevent source reuse.
The old DAG Lean attachment was stale after the upstream proof became available.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
