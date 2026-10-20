## What changed

Withdraw the unused Sheaf.CategoryTheory.MapExtendHomology duplicate, a depth-zero
retirement item in coord/retire-items.tsv. Retain all upstream declarations
verbatim. Reattach lem-weil-pbc-map-extend-homology to the canonical upstream
CochainComplex.mapExtendHomologyIso and record the existing Nonempty wrapper's
location in WeilConjectures.CategoryTheory.MapExtendHomologyExtension.

Change record: coord/changes/A3-retire-map-extend-homology.md.

The original item compiled via lcompile.py (1.3 seconds). Scratch Verify.lean also
compiled (1.3 seconds): rfl identifies the upstream construction with the retired
composite, the upstream theorem supplies degree zero, and #print axioms reports
only propext, Classical.choice and Quot.sound for both retained declarations.
tools/downstream.py confirms zero downstream modules; rg independently confirms
no imports of the retired path, so there are no adapted consumers.
Searches via msearch.py: Loogle found extendHomologyIso and its API; LeanFinder
found related extension naturality lemmas; grep returned no hits. Direct rg found
the complete upstream construction and the Nonempty wrapper in its extension module.

## Proved and sorry left

Actual hole count before: zero. After: zero. Holes closed: zero. Holes added:
zero. No split-off results. The retired declarations mapExtendHomologyIso and
mapExtendHomology_nonempty_iso were already proved; they remain available from
upstream as CochainComplex.mapExtendHomologyIso and mapExtendHomology_nonempty_iso,
respectively. This is a duplicate retirement, not a new proof or decomposition.

## No longer needed

Sheaf.CategoryTheory.MapExtendHomology is no longer needed and is withdrawn.
Its public imports Mathlib.Algebra.Homology.Embedding.ExtendHomology and
WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap disappear from the
empty historical module. These dependencies remain needed by the retained
upstream construction and are not claimed as globally pruned.
The DAG node remains and points at the upstream construction; no mathematical
lemma or unit step is removed. No remaining consumer imports the retired module.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief described a hole to prove, but the current item has
zero holes and is explicitly listed as a retirement. Earlier reports repeatedly
changed an already proved wrapper; this delivery instead removes the duplicate.
The retirement inventory's API note says the twin lacks the Nonempty theorem;
that theorem already exists in MapExtendHomologyExtension. The DAG attachment
still named the redundant Sheaf implementation, despite its audit already
identifying the proved canonical upstream isomorphism. This attachment is fixed.
No source-library signature, public import, definition body or target is changed.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
