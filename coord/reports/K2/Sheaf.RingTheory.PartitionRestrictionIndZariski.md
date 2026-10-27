## What changed

Completed `WContractification.PartitionRestriction.partition_restriction_ind_zariski`
without changing its statement, public definitions, or public imports. Added proved private
helpers for principal blocks, their finite presentability, fixed-base filtered-colimit
closure, and refinement maps. The product comparison uses the existing source-library
`CommAlgCat` IPC instance; the final colimit uses Mathlib `ObjectProperty.ind_ind`.
The node proof and dependencies now describe this route.

## Proved and sorry left

Closed 1 of 1 holes:
`WContractification.PartitionRestriction.partition_restriction_ind_zariski`
(node `lem-pe-partition-restriction-ind-zariski`). Added 0 holes; 0 remain in this packet.
This is a proof from existing declarations, including the still-stated
`ClopenRestriction.canonical_localization` and `ClopenRestriction.restriction_naturality`.
All private helpers have complete proofs. Empty S uses the empty quotient and Fin 0;
no nonempty-part or nontrivial-ring assumption was introduced.

## No longer needed

Removed proof imports `Sheaf.RingTheory.IndEtaleStability`,
`Mathlib.Algebra.Category.Ring.FilteredColimits`,
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`, and
`Mathlib.CategoryTheory.Limits.Constructions.Over.Connected`.
Added proof imports `WeilConjectures.Mathlib.Algebra.Category.CommAlgCat.Basic`,
`Mathlib.CategoryTheory.ObjectProperty.Ind`, and
`Mathlib.Algebra.Category.Ring.FinitePresentation`.

The proof no longer directly needs nodes
`lem-weil-pbc-filtered-colimit-algebras-elementwise`,
`lem-pc-filtered-colimit-commrings-elementwise`, or
`lem-weil-pbc-ind-etale-stability`: the source-library IPC instance supplies the
comparison and finite presentability plus ind_ind proves fixed-base closure.
Removed the latter node from this node's top-level tool_uses approval list.
No whole Lean module is withdrawn; source-library declarations and the unit route stay.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface repair was needed. The planned elementwise comparison
proof duplicated an existing IPC instance. The general varying-base arrow-category
stability theorem was stronger than needed for the final fixed-base colimit.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
