## What changed

Restored the complete archived module
Sheaf.CategoryTheory.CartanEilenbergGoodCutDecalage, byte-for-byte. Repaired its
import closure by changing the public DoubleComplexTotal provider from Sheaf to
WeilConjectures in GoodTruncationTotalBoundaryImage, GoodTruncationTotalImage,
and GoodTruncationTotalDecalage. In two private proofs of BoundaryImage,
DecreasingFiltration.step becomes PBCDecreasingFiltration.step. These are the
only edits to existing active modules; all are unclaimed.

The good-cut theorem still constructs its isomorphism using the left-exact
truncation comparison, the pure good-truncation/decalage comparison, the finite
mapped-total comparison and naturality of total symmetry. Its square is proved
by cancelling the mapped-cut comparison and composing their inclusion equations.
The existing lem-sp-ce-good-cut-decalage attachment and all proof dependencies
remain unchanged. Source read: Stacks derived.tex, remark-final-functorial (015X),
second filtration, and the existing dependency declarations and proofs. The
attached unit has no realized statement or step imposing another proof route.

All four modules compile cleanly through the required remote lcompile.py, in
11.8, 6.2, 5.4, and 13.6 seconds. The unchanged quarantined consumer CartanEilenbergGoodCutIdentification
also compiles cleanly against the packet in 10.9 seconds and is not delivered. Record: coord/changes/W3-cartan-eilenberg-good-cut-decalage-imports.md.

## Proved and sorry left

This is a quarantine/import repair of an already fully proved theorem, not a new
hole closure. Restored CategoryTheory.cartanEilenberg_good_cut_decalage
(lem-sp-ce-good-cut-decalage), with both private helpers still proved.
Original item holes: 0. Holes closed: 0. Holes added: 0. Split off: 0.
No sorry remains in the item or any of the three adapted modules.

The retained dependency theorems are
HomologicalComplex₂.good_truncation_total_boundary_image
(lem-sp-good-truncation-total-boundary-image),
HomologicalComplex₂.good_truncation_total_image
(lem-sp-good-truncation-total-image), and
HomologicalComplex₂.good_truncation_total_decalage
(lem-sp-good-truncation-total-decalage), all with their complete proofs retained.

## No longer needed

Removed public import Sheaf.CategoryTheory.DoubleComplexTotal from the three
adapted comparison modules; replaced it by the adopted upstream provider.
The duplicate Sheaf module is no longer in this packet's import closure. It is
not withdrawn: other consumers still use it. No mathematical node is pruned,
and no planned proof dependency or unit step is bypassed. No new nodes.

Searches through the required msearch.py found Mathlib's truncLE API but no
full good-cut/decalage theorem; the library already has the complete archived
argument, so no new proof route or intermediate theorem is needed.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantined repair with zero holes, rather than an unfinished
proof to split again. The archive itself is complete. The failure was the
mixed Sheaf/upstream DoubleComplexTotal import closure after synchronization.
The two providers define precisely the same finite image-supremum steps in
secondFiltration, but package them in different filtration types. Selecting the
upstream provider fixes the collision without changing the comparison statements.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
