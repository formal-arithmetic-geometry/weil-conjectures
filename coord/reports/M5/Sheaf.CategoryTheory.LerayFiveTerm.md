## What changed

Restored `lean/Sheaf/CategoryTheory/LerayFiveTerm.lean` from its upstream-sync
quarantine and proved all five original theorem holes, preserving every public
signature and every definition body. Added only proved private helpers.

The proof follows the existing node `lem-pqf-leray-five-term`: use the canonical
cycle/boundary recursion to stabilize the low-degree entries; identify their
limiting subobjects with the kernel and image of the original page-two
differential; use separatedness, exhaustiveness and the canonical convergence
comparison to bound the image filtration; and combine the four consecutive
exact pairs. The edge maps remain the original canonical constructions.

Replaced the redundant private import list by a public import of
`WeilConjectures.CategoryTheory.ExactCoupleConvergence`, which supplies the types
used in the public signatures. Retained the private proof import
`WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits`. Removed the redundant
private `Mathlib.CategoryTheory.Abelian.Exact` import during the return repair:
that API is already publicly provided by `ExactCoupleConvergence` through
`ExactCouple`.

Repaired the 2026-10-20 14:12 UTC stale-base return for delivery head
`5950675cff` (old base `6488bba00`). Read the current return, claim and rework
records, then reconstructed this file from the current preserved source at
`quarantine/Sheaf/CategoryTheory/LerayFiveTerm.lean`, applying the five complete
proofs and import repair. A programmatic comparison checks all nine public
declarations: the five theorem signatures, their docstrings, and the four
complete definitions are byte-for-byte unchanged. The reconstruction also
checks that there are no removed declarations, remaining holes or lines longer
than 100 characters. The current source is still the five-hole quarantined
module, so this packet restores and proves that source.

Compiled the module cleanly through `lcompile.py` against the current server
library (1.9 seconds). A fresh `#print axioms` probe of all five completed
theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.
Both new direct import edges pass `tools/import_direction.py may`.
Rechecked active and quarantined Lean consumers: the sole direct consumer is
the preserved `Sheaf.AlgebraicGeometry.LerayLowDegree`, whose statements and
canonical maps require no adaptation. The change record is
`coord/changes/M5-leray-five-term-public-import.md`.

## Proved and sorry left

Closed 5 original holes, all belonging to `lem-pqf-leray-five-term`:

- `CategoryTheory.BigradedExactCouple.limitCycles_bottom_eq_top`.
- `CategoryTheory.BigradedExactCouple.limitBoundaries_left_comp_eq_zero`.
- `CategoryTheory.BigradedExactCouple.imageFiltration_ofLE_eq_zero`.
- `CategoryTheory.BigradedExactCouple.imageFiltration_zero_eq_top`.
- `CategoryTheory.BigradedExactCouple.lerayFiveTerm`.

Added 0 holes; 0 holes remain; no result is split off. All private helpers are
proved. Public statements and constructions are unchanged.

## No longer needed

Removed the following direct proof imports:

- `Mathlib.CategoryTheory.Abelian.Exact`: already publicly imported by
  `ExactCouple`, which is publicly imported by `ExactCoupleConvergence`.
- `Sheaf.CategoryTheory.ExactCouple`: no derived-map compatibility lemmas used.
- `Sheaf.CategoryTheory.Filtration`: uses the existing PBC filtration API of the
  convergence data, without the separate compatibility declarations.
- `WeilConjectures.Algebra.Homology.ExactCouple.Basic`: its distinct general
  exact-couple representation is unused.
- `WeilConjectures.CategoryTheory.Abelian.Filtration`: its distinct filtration
  representation is unused directly.
- `WeilConjectures.CategoryTheory.ExactCouple`: already publicly imported by
  `ExactCoupleConvergence`; its actual exact-couple definitions are still used.
- `WeilConjectures.CategoryTheory.PBCFiltration`: already publicly imported by
  `ExactCoupleConvergence`; its filtration definitions are still used.

The direct import of `ExactCoupleConvergence` becomes public rather than being
removed. No existing DAG proof dependency is pruned: `def-sp-exact-couple`,
`def-sp-convergence`, and `def-sp-filtration` are all used. No upstream
declaration is removed or weakened. There are no new nodes or modules.

## Where the brief, the DAG or earlier work was wrong

The item file was in `quarantine/Sheaf/CategoryTheory/LerayFiveTerm.lean`, not at
its usual library path: `coord/rework.tsv` records the upstream-sync failure.
Its public declarations used `BigradedExactCouple` and the convergence API
through private imports, producing the recorded unknown-identifier error.
The public convergence import repairs that visibility error. No mathematical
statement repair or change to the planned route was necessary.

The returned delivery was rejected because the item changed on the shared
branch after base `6488bba00`, despite the previous packet's source check.
This repair explicitly reapplies the proof to the current quarantined file and
regenerates the packet with `deliver3.py`. The source declarations, canonical
edge-map constructions, DAG attachment and dependency route are preserved.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
