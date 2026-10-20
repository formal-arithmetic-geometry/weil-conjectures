## What changed

Retired Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFormalZeroSliceSplit,
as assigned in coord/retire-items.tsv. Its existing DAG node now attaches to the
proved theorem of the same name in
WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationFormalZeroSliceSplit.
Upstream drops only the unused hs and hmin hypotheses. A scratch theorem with
the entire old signature is proved by one application of the upstream theorem.
The punctured-split parent node now records the actual upstream call. Its Lean
consumer already imports upstream and supplies the correct argument list.
No upstream source or target signature is edited.

Change record:
coord/changes/retire-stalk-normalization-formal-zero-slice-split.md.

## Proved and sorry left

Baseline item: zero sorry. Holes closed: none (0 of 0); holes added: none;
split off: none; sorry left in delivered Lean: none. This is duplicate retirement,
not new proof progress. The existing theorem
AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_formal_zero_slice_split
is preserved upstream. The exact old signature is checked by a proved scratch
specialization; the unchanged upstream punctured-split consumer is also compiled.
Both the upstream theorem and the old-signature specialization use only propext,
Classical.choice and Quot.sound, as checked with #print axioms. The unchanged
parent compiles cleanly in 6.4 seconds.

## No longer needed

The entire duplicate module
Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFormalZeroSliceSplit is
withdrawn through deleted.txt. There are no remaining direct Lean imports to
rewrite. The mathematical node lem-sbc-stalk-normalization-formal-zero-slice-split
is retained and redirected upstream; no mathematical dependency node is pruned.
Its two proof dependencies, lem-sbc-section-finite-etale-generic-split and
lem-sbc-relative-normalization-smooth-base-change, remain used upstream.
All imports of the withdrawn copy disappear with that copy; equivalent imports
are already present in the existing upstream implementation. No retained module
has an import removed.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief describes proving holes, but the current assignment is
listed as a retirement and the item already compiles with zero sorry. The old
retirement inventory still names a Sheaf punctured-split consumer which has since
been retired; the live parent and its DAG attachment are upstream. The child
attachment was the stale remaining reference. The upstream theorem is stronger
only by dropping hs and hmin, and specializes to the exact old statement without
changing any definition or conclusion. No unit route is bypassed.

Required msearch searches ran: LeanFinder returned eight normalization and etale
algebra candidates but no full zero-slice theorem; Loogle returned seven
normalizationPullback API declarations; grep found normalizationPullback_snd.
The direct source comparison supplies the complete existing upstream theorem.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
