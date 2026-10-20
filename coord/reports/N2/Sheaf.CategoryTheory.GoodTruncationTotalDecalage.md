## What changed

Restored `lean/Sheaf/CategoryTheory/GoodTruncationTotalDecalage.lean` from its
quarantined archive, preserving its public theorem and every hypothesis.
Migrated its public DoubleComplexTotal import to
`WeilConjectures.CategoryTheory.DoubleComplexTotal`. Applied that same import
migration to the unclaimed modules `GoodTruncationTotalBoundaryImage` and
`GoodTruncationTotalImage`. The boundary lemma's two private calculations now
unfold `secondFiltration` directly, without the old `DecreasingFiltration.step`
accessor. No source-library file is changed.

This is a concrete compatibility repair: the archived consumer imports upstream
CartanEilenbergPresentation, which already imports upstream DoubleComplexTotal.
Previously importing our comparison also loaded the duplicate Sheaf implementation
and failed on `HomologicalComplex₂.secondFiltration_graded`. With the migrated
three-module chain, the unchanged archived consumer compiles (10.2 seconds).
The upstream filtration packages its steps in `PBCDecreasingFiltration`; its
second-filtration step is exactly the same finite supremum of diagonal images.
Our public statements use only these step subobjects, so all theorem signatures
and their mathematical meanings are preserved.

Simplified the private degreewise isomorphism to Mathlib's
`Subobject.isoOfMkEqMk`, replacing composition through a representative subobject.
Its monic-inclusion equation still proves the differential compatibility and
assembles the required complex isomorphism. Updated only the owned proof and
proof_origin fields of `lem-sp-good-truncation-total-decalage`; dependencies and
unit realization stay in place.

Change record: `coord/changes/N2-good-truncation-total-decalage-upstream-imports.md`.

## Proved and sorry left

This rework assignment starts with zero sorries. Closed 0, added 0, remaining 0;
there is no decomposition or split-off theorem.

The restored `HomologicalComplex₂.good_truncation_total_decalage` is fully proved.
The existing proofs of `HomologicalComplex₂.good_truncation_total_image` and
`HomologicalComplex₂.good_truncation_total_boundary_image` remain complete.
All private helpers remain proved. The three changed modules compile cleanly on
the compile server. Printing axioms of the restored theorem reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

The unchanged quarantined direct consumer
`Sheaf.CategoryTheory.CartanEilenbergGoodCutDecalage` compiles against the repair.
It was used only as a compile probe and is not included in this delivery.

## No longer needed

Removed `public import Sheaf.CategoryTheory.DoubleComplexTotal` from the item and
both image lemmas, replacing each with the adopted upstream module. Thus the
Sheaf duplicate is pruned from this comparison's import closure. Its global
withdrawal is not part of this delivery; it is held by S2.

No mathematical dependency node is pruned: `def-sp-double-complex-total` still
supplies the same total and finite-supremum filtration formulas, now through the
adopted source implementation. The decalage and both image lemmas remain needed.
No other imports are removed, no module is withdrawn, and no node is deleted.

## Where the brief, the DAG or earlier work was wrong

The item source is absent because of quarantine, not withdrawal. Its archive and
Lean attachment are preserved, and no deleted.txt is used. The archived item
already has zero sorries; this is an import compatibility repair rather than a
new proof-hole closure.

The first compile reproduced the recorded duplicate-filtration error. Rebuilding
unchanged current decalage dependencies made the item compile, but the consumer
check then exposed the duplicate DoubleComplexTotal declarations. The final
import migration repairs that second conflict too. Unchanged dependency copies
were used only to compile current sources and are excluded from the packet.

The definition node still records the older Sheaf DoubleComplexTotal module;
its currently claimed S2 repair is separate. This delivery retains that
mathematical dependency and uses the existing upstream declarations, with no
modification to the claimed module or its node attachment.

Searches: LeanFinder found generic monicity results, no shorter comparison;
Loogle did not index Subobject.isoOfMkEq; source grep located Mathlib's proved
Subobject.isoOfMkEqMk, used for the private simplification. Import-direction
checks permit all three migrated imports. No new mathematical assertion or
source-library exception is required.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
