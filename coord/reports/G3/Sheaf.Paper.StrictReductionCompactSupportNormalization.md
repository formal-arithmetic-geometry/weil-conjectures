## What changed

Proved `AlgebraicGeometry.Scheme.StrictSupportNormalization.kappaTarget_composition`.
Its proof combines the existing `kappaTarget_reduction` and `inputPull_composition`
with naturality of `supportScalar`. A proved private categorical helper performs
cancellation before specialization, keeping the large derived constructions out of
the calculation. The same target reduction and its inverse cancel at the intermediate
object, yielding the required compositor equation.

Statements, definitions, public imports, and the unit route are unchanged. No
experimental coefficient-alias or instance-representation changes are included.

Validation: the final module compiled against the project baseline in 31.5 seconds.
All original public signatures were compared and are unchanged; all lines fit the
100-character limit.

Search: LeanFinder located categorical isomorphism cancellation lemmas. Source
searches covered Mathlib categorical isomorphisms, existing proper/open mate
normalizations, refinement coherence, and the reduction/pullback composition API.

## Proved and sorry left

Closed 1 of the 14 original holes: `kappaTarget_composition`.
Added 0 holes; split off 0 statements. All names below are in
`AlgebraicGeometry.Scheme.StrictSupportNormalization`.

The 13 unchanged holes are:

- `strictReductionCompactSupportNormalization`
- `scalarPull_composition`
- `inputPull_composition`
- `refinement_normalization`
- `refinement_cocycle`
- `targetRefinement_normalization`
- `refinement_exchange`
- `inputPull_identity`
- `refinement_isIso`
- `commonRefinement_normalization`
- `commonRefinement_coherence`
- `scalarPush_composition`
- `sourceRefinement_normalization`

Every remaining hole belongs to the existing node
`lem-pur-strict-reduction-compact-support-normalization` and retains its source and
natural-language proof. The completed proof uses `inputPull_composition`, which
remains an existing named obligation; it does not claim that dependency is axiom-free.

## No longer needed

None. No imports, nodes, or modules are withdrawn. The proof follows Steps 6--7 of
the existing normalization plan. The remaining obligations retain their dependencies,
so no DAG route or dependency changes are needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement discrepancy found. The target-composition calculation
closes from the stated reduction and input-composition interfaces.

Additional candidate refinement proofs encountered expensive kernel comparisons
between the reduction, exchange, and constant strict-tower category presentations.
An experiment aligning completed-ring aliases did not resolve those comparisons;
changing derived-instance wrappers then exceeded the supporting file's time limit.
Neither experiment is included in this delivery, and no unverified refinement proof
is claimed. The actual corners and original remaining proof plans are preserved.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
