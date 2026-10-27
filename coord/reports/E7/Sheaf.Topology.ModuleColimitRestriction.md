## What changed

Proved `TopologicalSpace.Opens.module_colimit_restriction` without changing its statement.
Mathlib's `SheafOfModules.overPushforwardOverAdj` gives preservation of colimits by
restriction. The proved adopted-library theorem
`CategoryTheory.moduleSheaves_colimits_forgetful` supplies a colimit cocone with its
canonical comparison to the sheafified sectionwise colimit. Composing its comparison
isomorphism with uniqueness of colimits gives the required map. Its coprojection equations
follow by faithfulness and cancellation; uniqueness follows from the presheaf-colimit
universal property and injectivity of `sheafificationHomEquiv`.

Added one proved private helper for the cancellation calculation. Replaced the two private
proof imports with `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
Updated the item's node proof and dependencies to reflect this route. No public signature,
definition, public import, or consumer changed.

## Proved and sorry left

Closed the sole original hole: `TopologicalSpace.Opens.module_colimit_restriction`
(`lem-weil-pbc-ringed-space-colimit-restriction`). Holes closed: 1. Holes added: 0.
No `sorry` remains in the delivered module and none is split off.
The private helper `TopologicalSpace.Opens.sheafification_fac` is also proved.

## No longer needed

Removed private imports `Sheaf.Topology.OpenRestrictionAdjunction` and
`Sheaf.CategoryTheory.RingedSiteModules`. The node
`lem-weil-pbc-ringed-space-open-restriction-adjunction` and its unfinished declaration
`TopologicalSpace.Opens.exists_openRestrictionAdjunction` are no longer proof dependencies
of this item: their explicit sectionwise transpose formulas are unnecessary for colimit
preservation, because Mathlib already constructs the needed adjunction.
`RingedSiteModules` is unnecessary because the statement uses Mathlib's module category
directly. These are dependency removals for this item; other consumers may still need the
modules. No module is withdrawn. All other declared proof dependencies remain used through
the sheafified-colimit construction, sheafification, and the colimit universal properties.

## Where the brief, the DAG or earlier work was wrong

The planned mathematics is correct. The Mathlib search notes already mentioned
`overPushforwardOverAdj`; its direct specialization suffices without proving the stronger
sectionwise-formula theorem. The adopted source theorem for module-sheaf colimits is proved
and exposes exactly the coprojection equations needed here. The unit route is unchanged.
The proof makes no nonempty-diagram or nonempty-open assumption and handles the empty
indexing category and empty open by the same universal properties. No new nodes or
interface repairs were necessary.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
