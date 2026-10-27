## What changed

Proved `AlgebraicGeometry.ProEtale.RationalP1.scalar_p2_chern_homology_criterion`
with its original signature. The delivery adds one fully proved module,
`Sheaf.Paper.DiagonalCompletedChernSplitting`, and proved private helpers.
The proof lifts the given tower splitting to completed coefficients, transports it
through the specified realization and coefficient mates, and obtains a scalar
splitting with the prescribed Chern component. Homology gives the concentration
and Chern conclusions. The diagonal section makes the specified twisted unit split
mono. Its degree-minus-two homology has rank-one source and target, so the existing
local rank-one epi criterion applied to its retraction makes it invertible.

The new completed-splitting module imports the existing tower component identities,
coefficient-limit comparisons, and completed-Chern completeness helpers. The item
imports that proved lift, the common root cover, and the local rank-one criterion.
Updated the item's DAG proof, dependencies, and proof origin for this argument. No existing definition, theorem statement, public import,
instance, or shared source-library module was changed.

Searches: LeanFinder found no matching scalar projective-line splitting; Loogle
located the single-functor and homology comparisons; Mathlib grep found no direct
concentration theorem. Local source searches found the proved twisted tower
splitting and the proved local rank-one epi criterion, which this proof uses.
The covering argument includes the empty scheme and zero section rings.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.RationalP1.scalar_p2_chern_homology_criterion`.
There are zero `sorry` occurrences in the two delivered Lean modules, zero added
holes, and no split-off holes. The new public theorem
`AlgebraicGeometry.ProEtale.RationalP1.completed_chern_splitting` and every new
private helper have complete proofs.

Both delivered modules compile through `lcompile.py`: the completed splitting
module in 37.3 seconds and the final criterion in 54.7 seconds. Debug profiling
options have been removed; the final criterion compile reports no warnings.

## No longer needed

None of the original declared proof dependencies is pruned: the tower component
identities, scalar maps, and reference are all used. No original import was
removed. The temporary exploratory import of
`Sheaf.Paper.RationalP1ScalarChernP2Degree` was removed because the transported
splitting itself proves the degree-zero Chern assertion. No library module is
withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original DAG planned a direct identification of the transported first
component with the specified twisted unit. That comparison is unnecessary. The
transported splitting identifies the target homology with the line; the diagonal
section and local rank-one argument then prove invertibility of the specified
unit without choosing or identifying its first component. This stays within the
unit's tower-splitting route. There is no statement repair and no change to the
unit's statement or proof steps.

## New nodes

`lem-sfb-diagonal-completed-chern-splitting`, realized by
`Sheaf.Paper.DiagonalCompletedChernSplitting`, states and proves the completed
splitting with prescribed normalized Chern component and an unspecified first
component. This is the completed-coefficient part of the main proof, with no new
hole. The module also contains proved private helpers for additive realization,
scalar extension and postcomposition of such splittings. Profiling first led to
explicit biproduct simplification, folded derived functors, and an explicitly typed adjunction; the self-contained completed lift
was then factored out so each module can compile within the file limit.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.DiagonalCompletedChernSplitting": "101bf3c096b9d0529c703a05c9e8092d62c3e4d0", "Sheaf.Paper.RationalP1ScalarChernP2HomologyCriterion": "97902f0242b7f6dc2e0ca4ba5bcce432df6a3753"}, "results": {"Sheaf.Paper.RationalP1ScalarChernP2Splitting": {"hash": "23f89058e1310547bf527b4573fd1075ba85290f", "status": "OK"}}, "seconds": 23, "time": "2026-10-28T05:40:13+0800", "transitive": 0, "version": 1}
```

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
