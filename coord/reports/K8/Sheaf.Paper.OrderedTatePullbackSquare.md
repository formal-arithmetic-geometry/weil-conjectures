## What changed

Proved `AlgebraicGeometry.Etale.orderedTatePullbackSquare` by cancelling the
forward comparison for `s'` and using the ordered coefficient composition law
on the two composites `b ≫ s` and `s' ≫ v`. Added the proof-only import
`Sheaf.Paper.OrderedTateCoefficientComposition`. The ordinary pullback
functoriality and the inverse/forward identities close the remaining category
algebra. Updated the item's node proof to record this route.

## Proved and sorry left

The original hole in `orderedTatePullbackSquare` is closed. One strictly simpler
intermediate theorem was added with its proof intentionally split off:
`AlgebraicGeometry.Etale.orderedTateCoefficientComposition` remains `sorry` in
`Sheaf.Paper.OrderedTateCoefficientComposition`; its node is
`lem-pur-ordered-tate-coefficient-composition`.

## No longer needed

No imports were removed and no existing modules or declarations were pruned.
The original direct plan dependency is packaged by the new composition node.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan described the full induction directly in the square
node, but the square is an immediate categorical cancellation once the strictly
simpler ordered coefficient composition law is stated. The node was updated to
record this decomposition and its actual proof dependency.

## New nodes

`lem-pur-ordered-tate-coefficient-composition` — composition of the ordered Tate
coefficient pullback for two composable scheme maps. The declaration and its
source/proof plan are in `lean/Sheaf/Paper/OrderedTateCoefficientComposition.lean`;
no change record was needed.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
