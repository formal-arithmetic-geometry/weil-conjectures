## What changed

Proved the three original theorems in
`Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted`.
The counit proof specializes the published K-flat computation. The unit-map theorem
constructs the normalized adjunction unit degree by degree and uses sectionwise
extensionality for uniqueness. The tower theorem uses the stated common K-flat roof,
naturality of the localized derived counit, the exact-restriction factorization,
and unit/transition naturality followed by cancellation.

Constructed `unrestrictedTowerUnit` directly from that adjunction unit, preserving its
signature and pure-tensor formula. Added the proved formula theorem
`unrestrictedTowerUnit_condition` and the equality to the former chosen family
`unrestrictedTowerUnit_eq_chosen`. The change record is
`coord/changes/P3-unrestricted-tower-unit-construction.md`.
The node records the actual use of the published scalar-reduction witness and the
normalized adjunction API. Its declaration list also records the proved unit-formula
and equality theorems, which express the unit already specified by that node.
No target statement changed.

## Proved and sorry left

Closed `WeilConjectures.unrestrictedTowerCounit_isIso`,
`WeilConjectures.unrestrictedTowerMaps_existUnique`, and
`WeilConjectures.unrestrictedReductionTowerWellDefined`, all attached to
`lem-weil-integral-reduction-tower-well-defined`: 3 of 3 original holes closed.
No holes remain in the item and no holes were added or split off. The proof uses
the project's stated dependency declarations, including those not yet proved.

## No longer needed

Removed the proof imports
`Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass` and
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
The resolving-class existence theorem `lem-pur-left-derived-from-kflat-class` is
not needed directly: the published scalar-reduction witness already contains the
universal derived pair and its K-flat computation. The DAG's corresponding direct
proof dependency was removed. The derived-change-of-rings node itself remains needed
through that witness. No unit statement or unit proof step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The retained report said the abandoned helpers had been removed, but the sandbox
still contained them and profiling settings. Those drafts were corrected and the
entire planned argument was completed. The choice-based unit definition made component
calculations unfold the inverse-limit coefficient sheaf; its direct construction and
named formula avoid that unfolding. Independently sized site and coefficient universes
are retained throughout.

## Forced adaptations

`Sheaf.Paper.IntegralReductionTowerCanonical` is unclaimed. Its proof of
`canonicalIntegralReductionTowerMap_naturality` obtains the unit formula from the old
choice expression. Replaced only that proof line by the new formula theorem; the
statement and all definitions of the consumer stay identical. The original fails at line 95:
`Type mismatch: Exists.choose_spec ... has type unrestrictedTowerUnitCondition ...
choose, but is expected to have type unrestrictedTowerUnitCondition ...
(unrestrictedTowerUnit l E Y P)`.
The only adapted line replaces `(unrestrictedTowerMaps_existUnique l E Y P).exists.choose_spec`
by `unrestrictedTowerUnit_condition l E Y P`.
`Sheaf.Paper.IsomorphismReductionTower` (currently held by B2) compiled without source changes
and is not included in the delivery. The adapted canonical tower compiled in 9.3 seconds;
the item compiled in 45.6 seconds and the unchanged isomorphism tower in 15.6 seconds.

The DAG is acyclic below the updated node (250 reachable nodes checked). Its canonical
tower definition depends on the present lemma, so the proof uses only the earlier
strict transition's natural-transformation type rather than adding that later canonical
tower node as a dependency.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
