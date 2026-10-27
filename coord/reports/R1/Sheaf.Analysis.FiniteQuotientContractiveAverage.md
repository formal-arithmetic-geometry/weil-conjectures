## What changed

Proved `ContinuousMap.exists_finiteQuotientContractiveAverage` in
`Sheaf.Analysis.FiniteQuotientContractiveAverage`, preserving its entire statement.
Added a private proof import of `Mathlib.Algebra.CharP.Algebra` and proved private
helpers for finite averages, their linearity and normalization, compatibility
under surjective group homomorphisms, and the ultrametric finite-sum bound.

Constructed the actual submodule of functions factoring through open normal
quotients. Its membership proofs supply quotient representatives; independence
under common refinement makes their normalized averages into a linear map.
The norm estimate uses coprimality, the p-adic norm formula, and the isometric
algebra map. Left and right translations are explicit continuous functions,
with their averages equal by reindexing. No data is chosen from an unproved
theorem. Updated the item's DAG proof to reflect the double-sum refinement
argument and direct supremum-norm bound.

## Proved and sorry left

Closed the one original hole:
`ContinuousMap.exists_finiteQuotientContractiveAverage`
(node `lem-sfb-finite-quotient-contractive-average`).
Added zero holes; zero sorries remain. This is a proof, not a decomposition.

## No longer needed

No project modules or nodes are pruned; no imports were removed. Both stated
conceptual dependencies remain used: p-adic scalar facts and explicit universes.
Step 3's explicit fiber bijections/cardinality computation is replaced by
interchanging two finite sums and reindexing by group translations. Step 5's
finite maximum is replaced by bounding each term directly by the function norm.
The open-normal basis hypothesis is not needed for this finite-level assertion;
it remains unchanged in the theorem's signature. Density of the subspace,
which would require that basis, is outside this item.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement change. Mathlib's open normal subgroups
have no top instance, so the proof explicitly constructs the whole group as an
open normal subgroup when representing constants. No other module is changed,
and no shared interface is changed, so no consumer adaptation is necessary.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
