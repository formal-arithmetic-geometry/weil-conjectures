## What changed

Restored Sheaf.AlgebraicGeometry.PicardDerivedUnitNormalizationComposition from
its coord/rework.tsv archive, preserving the definition and composition theorem.
Qualified AlgebraicGeometry.derivedPullback in the private naturality helper to
avoid the adopted Scheme.Modules.derivedPullback name collision. Local
irreducibility annotations in the private-helper namespace avoid needless
unfolding of tensorPullback and Adjunction.leftAdjointUniq; they export no
attributes. Both public signatures and the actual normalization construction remain unchanged. The proof
keeps the existing DAG route, so neither node requires a dependency update.

Searches used the required msearch.py leanfinder, loogle and grep routes.
Lean Finder returned ordinary pullbackComp but no derived normalization theorem;
Loogle and grep found pullbackObjUnitToUnit and its ordinary adjunction equations.
The local library search found the existing pinned single comparison and
composition theorem, which the restored proof uses. Read Stacks cohomology.tex
at lemma-derived-pullback-composition and remark-base-change (0D5S and 08HY).

Change record: coord/changes/J1-picard-derived-unit-normalization-restoration.md.

## Proved and sorry left

This assigned restoration starts with zero sorry holes. The restored
AlgebraicGeometry.Scheme.picardDerivedUnitNormalization_comp and both private
helpers have complete proofs. The normalization definition has its original
explicit construction. Holes closed: 0; holes added: 0; holes left: 0. No result
is split off.

The final module compiles cleanly through lcompile.py in 32.9 seconds (60-second
limit). A byte comparison against the archive verifies that both public
declarations, including their bodies, are unchanged. All Lean lines are at most
100 characters. Both quarantined consumers and the complete DAG parent list
were inspected; no public interface change forces an adaptation.

## No longer needed

None. All archived imports and both node attachments are preserved. The ordinary
pullback adjunction, canonical single comparison, and its composition identity
remain needed. Neither quarantined parent is withdrawn.

## Where the brief, the DAG or earlier work was wrong

This is a zero-hole restoration rather than an unproved theorem. The archive's
unqualified derivedPullback in Scheme.Modules resolves to a different functor
after the source synchronization. Its error compares Hom universes v and v + 1.
Qualifying the intended source functor repairs that mismatch. The DAG's
mathematical argument and the public statements remain valid, including identity
maps and empty schemes. Both direct consumers are still quarantined; their
restoration is independent and no consumer edit is forced by this repair.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
