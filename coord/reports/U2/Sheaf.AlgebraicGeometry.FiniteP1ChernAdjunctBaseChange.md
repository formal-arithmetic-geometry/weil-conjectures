## What changed

The target theorem now has a complete Lean proof by composing two strictly smaller
statements. `FiniteP1ChernMapBaseChange` isolates the inverse-image square for the
normalized Chern map, and `FiniteP1ChernAdjunctMate` isolates its formal transpose
under the projective-line adjunction. Both modules are imported privately by the
item. The target's proof applies the mate statement to the map square statement.

## Proved and sorry left

The target declaration `ordinaryFiniteP1_chern_adjunct_baseChange` is proved.
The two geometric/formal substeps remain split as named statements:

- `ordinaryFiniteP1_chern_map_baseChange` in node
  `lem-sp-finite-p1-chern-map-base-change` (sorry left).
- `ordinaryFiniteP1_chern_adjunct_of_map_baseChange` in node
  `lem-sp-finite-p1-chern-adjunct-mate` (sorry left).

No other declarations were added, and no sorry occurs in a definition.

## No longer needed

None. No import or declared proof dependency from the assigned node was pruned.

## Where the brief, the DAG or earlier work was wrong

The nearby `ordinaryFiniteP1_components_baseChange` statement concerns the
negative-twist Chern-adjoint component of the decomposition and does not have the
same source or target as the positive Chern pushforward in this item. It therefore
cannot discharge this target directly. The target proof has been split at the
actual inverse-image Chern square and its formal mate step.

## New nodes

`lem-sp-finite-p1-chern-map-base-change` records the geometric normalized Chern-map
square and is stated in
`lean/Sheaf/AlgebraicGeometry/FiniteP1ChernMapBaseChange.lean`.

`lem-sp-finite-p1-chern-adjunct-mate` records the formal adjunction transpose and
is stated in
`lean/Sheaf/AlgebraicGeometry/FiniteP1ChernAdjunctMate.lean`.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
