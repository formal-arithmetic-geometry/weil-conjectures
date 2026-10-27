## What changed

Proved CategoryTheory.StageSystem.faithful_hom_transport in
Sheaf.CategoryTheory.FaithfulStageHomTransport with the existing tr_zero, tr_add,
tr_tr, and tr_injective lemmas. Common upper bounds give a nonempty directed
common-stage subtype. The explicitly constructed additive maps are S.tr pointwise.
For self transport, apply tr_injective and the faithful functor's map_injective
to tr_tr at repeated indices. Composition is tr_tr.

Updated lem-pur-faithful-stage-hom-transport's proof description and proof_origin
to name the exact existing API used. Its statement, dependencies and Lean signature
are unchanged. No new nodes or declarations.

Removed the unused public import of Sheaf.CategoryTheory.ExactStagePairData.
The import change and consumer check are recorded in
coord/changes/F3-faithful-hom-transport-import.md.

## Proved and sorry left

Closed the one existing hole:
CategoryTheory.StageSystem.faithful_hom_transport
(node lem-pur-faithful-stage-hom-transport).

Holes closed: 1. Holes added: 0. Holes remaining in the delivery: 0.
No split-off statements and no decomposition.

Validation: the delivered Lean module compiled cleanly through lcompile.py in
1.9 seconds. tools/downstream.py reports zero downstream modules; its declaration
usage search finds only the item itself. The delivery tool performs the final
compile, interface checks and axiom audit.

## No longer needed

Removed import: Sheaf.CategoryTheory.ExactStagePairData. The theorem needs no
supplied exactness, shifts, pretriangulations, or common-stage triangle predicate.
No DAG dependency is removed: def-sf-directed-common-stage-data still supplies
its underlying stage-system notion, available through StageSystem.Preadditive.
The other two declared dependencies supply preadditivity and directed systems.
No module is withdrawn or declared globally unused.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The planned cocycle/naturality and bilinearity
calculations already exist as proved lemmas in the adopted stage-system library.
The faithful-reflexive argument uses no unitors or normalization, works at repeated
indices, and retains independent index, object and morphism universes. Empty stage
categories cause no issue because the theorem quantifies over supplied A and B.
The unused exact-stage import overstated the Lean dependencies; it is removed.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
