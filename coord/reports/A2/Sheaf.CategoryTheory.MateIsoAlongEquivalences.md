## What changed

Proved `CategoryTheory.isIso_mateEquiv_of_isEquivalence_of_fullyFaithful` in
`Sheaf.CategoryTheory.MateIsoAlongEquivalences`, with its statement and visibility unchanged.
The proof follows all six steps of `lem-weil-mate-iso-along-equivalences`: compose the
fully faithful Hom equivalences, the adjunction equivalences, and precomposition by the
component isomorphism; identify the result with postcomposition by the mate via
`mateEquiv_counit` and naturality of the given isomorphism; transport bijectivity using
`G.objObjPreimageIso`; and apply Mathlib's elementary two-sided inverse criterion
`isIso_of_yoneda_map_bijective`. Componentwise invertibility gives invertibility of the
natural transformation through `NatTrans.isIso_iff_isIso_app`.

The original import list is sufficient. No definitions, interfaces, consumers, or DAG
route were changed, and no change record or new node is needed.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.isIso_mateEquiv_of_isEquivalence_of_fullyFaithful`
(node `lem-weil-mate-iso-along-equivalences`).

Added 0 holes; 0 holes remain. No decomposition or split-off.
The complete module compiles cleanly through `lcompile.py`.

## No longer needed

No original imports, nodes, or modules were pruned. The node already had no project
proof dependencies. A temporary explicit import of `Mathlib.CategoryTheory.Yoneda`
was removed because the original public import of `Mathlib.CategoryTheory.Adjunction.Mates`
already supplies it transitively. The proof uses only Mathlib declarations and preserves
the existing elementary proof plan and the unit's route.

## Where the brief, the DAG or earlier work was wrong

None. All hypotheses and arbitrary object and morphism universes are preserved.
The chosen preimage of an object is obtained from Mathlib's proved essential-surjectivity
API; this delivery adds no chosen data or unproved existence theorem.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
