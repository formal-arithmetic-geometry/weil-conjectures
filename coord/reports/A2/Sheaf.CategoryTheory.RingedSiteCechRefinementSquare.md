## What changed

Decomposed the remaining cohomological roof theorem into two strict lower statements: a witness-level roof theorem and a normalized-edge uniqueness theorem. The original `ringedSite_cech_refinement_square_rest` now combines those declarations; its statement is unchanged. The new modules are imported privately by the proof.

## Proved and sorry left

The parent theorem was already proved in the base. The remaining `ringedSite_cech_refinement_square_rest` theorem is proved from the two new lower statements. The new declaration `ringedSite_cech_refinement_square_rest_witness` is the one remaining split-off sorry. The strict uniqueness declaration `ringedSite_cech_refinement_square_edges_unique` is proved by cancellation after identifying the augmentation maps. `ringedSite_cech_refinement_square_abelian` remains an original sorry.

## No longer needed

No existing planned dependency was removed.

## Where the brief, the DAG or earlier work was wrong

The parent tuple-map theorem had already landed, while the cohomological roof remained a separate unresolved component. The roof was split into witness construction and edge uniqueness so the parent statement can be assembled by a real Lean proof.

## New nodes

`lem-weil-pbc-ringed-site-cech-refinement-square-witness` and `lem-weil-pbc-ringed-site-cech-refinement-square-edges-unique` are new strict lower statements, each with its own module and DAG node.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
