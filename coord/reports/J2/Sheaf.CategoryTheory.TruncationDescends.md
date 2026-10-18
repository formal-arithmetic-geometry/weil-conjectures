## What changed

Proved `DerivedCategory.truncation_descends` in
`lean/Sheaf/CategoryTheory/TruncationDescends.lean`, preserving its entire public signature.
The proof follows all six existing steps of `lem-weil-pbc-truncation-descends`:

1. Mathlib's `CochainComplex.quasiIso_truncLEMap_iff` proves preservation of
   quasi-isomorphisms by both truncations. `quasiIsoAt_ιTruncLE` and `isZero_of_isLE`
   give the stated cohomology comparisons, including the boundary degree.
2. The homology and single-complex functors preserve the relevant isomorphisms.
3. `CochainComplex.exists_upperTruncationStepSES` supplies the inclusion, projection,
   their characterizations, and their naturality. The projection's naturality follows
   by composing the two quotient naturality equations supplied by that theorem.
4. `Localization.lift` and `Localization.fac` construct the three descended functors
   and comparison isomorphisms.
5. Two fully proved private helpers, `descent_iso_unique` and `descent_trans_unique`,
   specialize `Localization.fullyFaithfulWhiskeringLeft`: take the preimage of the
   conjugated isomorphism/transformation and use faithfulness and cancellation to
   prove uniqueness. These implement the existing localization-universal-property node.
6. Naturality of the descended transformations and comparison isomorphisms proves
   all remaining equations.

Read Stacks `homology.tex`, Section 0118 (`section-truncations`), the canonical upper
truncation and its cohomology formula; `derived.tex`, Remark 08J5
(`remark-truncation-distinguished-triangle`); and `categories.tex`, Lemma 04VG
(`lemma-properties-left-localization`), clause (3). The existing node already records
Mathlib's fully faithful precomposition formulation of the transformation clauses.
No statement, definition, DAG route, or unit route changed. No consumer adaptations
or change records are needed.

Validation: the final proof compiles cleanly with the prescribed `lcompile.py`.
A separate compilation with `#print axioms DerivedCategory.truncation_descends` reports
exactly `[propext, Classical.choice, Quot.sound]`. The diagnostic command was removed
before delivery. The public signature was compared verbatim with the original; all
lines have at most 100 characters. Semantic, Loogle, and grep searches were run using
`msearch.py`, and the library and Mathlib declarations were read before proving.

## Proved and sorry left

Closed 1 of 1 original holes: `DerivedCategory.truncation_descends`
(node `lem-weil-pbc-truncation-descends`).

Added 0 holes; split off 0 theorems. No `sorry` remains in the delivered module.
Both private helpers are proved. The main theorem's complete axiom audit contains
no `sorryAx`, including through its imported dependencies.

## No longer needed

Removed the redundant proof import `Sheaf.Algebra.Homology.UpperTruncationStepSES`.
It is a retired re-export of `WeilConjectures.Algebra.Homology.UpperTruncationStepSES`,
which is already imported directly and supplies the declaration used by this proof.
Only this import edge is removed; no claim is made that the wrapper is globally unused.

All four declared proof dependencies remain needed: `lem-weil-pbc-truncation-cohomology`,
`def-weil-abstract-derived-category`, `lem-weil-pbc-truncation-step-ses`, and
`lem-weil-pbc-localization-universal-property`. No DAG nodes are pruned, and no new
proof dependency or import is introduced.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original module imported both a retired re-export
and its source module; the duplicate import was unnecessary. The existing six-step
plan is fully realizable from the currently available declarations, with no splits.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
