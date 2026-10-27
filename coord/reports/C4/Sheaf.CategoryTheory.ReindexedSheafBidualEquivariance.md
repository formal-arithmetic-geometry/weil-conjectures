## What changed

Filled `SheafOfModules.reindexed_bidual_equivariance` with the slice reindexing,
coefficient transport, double contragredient calculation, and fixed-pair constructions
specified by its existing proof plan. All added helpers are private and proved.
The public statement, public imports, and definitions used by consumers are unchanged.

The slice-map bijectivity argument adapts the existing proved private
`restriction_map_bijective` argument in `Sheaf.CategoryTheory.ElementRestrictionHom`
to allow an isomorphism of coefficient presheaves. The comparison sends a localized
map to its reindexed components followed by the specified ring isomorphism.

## Proved and sorry left

Closed: `SheafOfModules.reindexed_bidual_equivariance`
(node `lem-sf-reindexed-sheaf-bidual-equivariance`), the module's sole original hole.
Added: zero holes. Left: zero holes. No statement was split off.

## No longer needed

None. All four original public imports are required by the unchanged statement.
The proof follows the five existing DAG steps and uses all four declared proof
dependencies through their existing definitions; no nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The argument works without any local
freeness or reflexivity hypothesis. Invertibility of bidual evaluation is used
only for the final conditional inverse and fixed-pair isomorphism.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
