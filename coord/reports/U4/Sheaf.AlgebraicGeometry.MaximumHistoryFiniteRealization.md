## What changed

Replaced the body of AlgebraicGeometry.maximumHistory_finite_realization by a complete
Lean assembly proof with the original signature and all realization fields unchanged.
The proof constructs a stopped chronology, supplies its lower-cut realization, and
proves uniqueness of the length by comparing regularity at the shorter endpoint.

Added MaximumHistoryChronology.lean. Its theorem
AlgebraicGeometry.maximumHistoryChronology_exists is proved, including a concrete
constant empty history, finite-prefix extension by Fin.snoc, and the dependent-choice
contradiction to the supplied termination clause. It derives admissibility, all center
and intermediate geometry, positive greatest-value labels, strict label monotonicity,
and the empty/regular input cases. All constructions have genuine data; no definition
uses an unproved existence theorem. Choices are made only inside the theorem proof.

Added two proper intermediate statements in their own modules:
MaximumHistoryLowerCutTower.lean constructs cut diagrams from a supplied stopped
chronology, and MaximumHistoryCommonStage.lean compares regularity at a common prefix
without assuming either terminal scheme regular. The item combines these statements
with the proved chronology and a symmetric strict-length contradiction. This is a
partial decomposition delivery; the canonical comparison theorem remains open.

No existing signature, definition body, public import, attribute, or other module was
changed. No existing declaration was moved. The new segment and chronology structures
are partial data needed before cut padding, not copies of FiniteMaximumLabeledHistory,
which already assumes a cut realization and its extra prefix identifications.

Validation: compiled through lcompile.py in dependency order. The stopped chronology
compiled in 10.8 seconds in the first successful run. Final compile results and the
mechanical delivery checks are recorded by deliver3.py.

## Proved and sorry left

Original holes: 2. Original hole closed: 1, by decomposition, in
AlgebraicGeometry.maximumHistory_finite_realization
(lem-trf-maximum-history-finite-realization). This theorem has a complete Lean proof
from the named intermediate statements, but is not claimed sorry-free transitively.

Additional proved theorem: AlgebraicGeometry.maximumHistoryChronology_exists
(lem-trf-maximum-history-chronology), with no sorry in the new chronology module.
Its private finite-segment termination theorem and every construction are proved.

Original hole left unchanged: AlgebraicGeometry.maximumHistoryRealization_comparison
(lem-trf-maximum-history-finite-realization).

Holes added: 2, each a public theorem with exactly a sorry body, full proof in words,
source, and its own DAG node:

- AlgebraicGeometry.maximumHistoryChronology_lowerCutTower
  (lem-trf-maximum-history-lower-cut-tower).
- AlgebraicGeometry.maximumHistorySegment_commonStage
  (lem-trf-maximum-history-common-stage).

Thus there are 3 sorry declarations in the delivered modules in total, versus the 2
original holes; the hole net is -1. This is a decomposition, not a net proof gain.
The finite-recursion, geometry, positivity, label monotonicity and endpoint arithmetic
are actual Lean proofs rather than additional holes.

## No longer needed

Removed direct proof imports from the item:

- Sheaf.AlgebraicGeometry.IsRegularScheme (already public through the history data).
- WeilConjectures.Blowup.BlowupUniversal.
- WeilConjectures.Compactification.StrictTransform.
- WeilConjectures.Blowup.Principalization.
- WeilConjectures.Blowup.InvertibleCenter.

The last four are not needed directly by the assembly proof. Their mathematical facts
remain in the DAG proof plans of the two split statements and the still-open comparison
theorem; strict-transform definitions also remain public through the existing data.
No existing node or module is withdrawn or claimed globally unnecessary. All three
original public imports remain verbatim. No adopted upstream declaration is changed.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The original Steps 1, 2 and 4 are now formalized.
The indexing and geometric comparison glue was not supplied by the existing dependency
signatures: the listed modules give the raw data and ordinary blowup tools. Those
remaining steps are now explicit independent items rather than hidden proof-body holes.

Read ILO VIII printed pp.86--87 and 91--94, especially 2.1.1--2.1.4, 2.3.1,
2.3.4--2.3.5(ii), 2.3.11 and 2.3.13. The conditional finite-recursion and lower-cut
arguments are marked as agent-written elaborations of those conventions and the
supplied calculus, not as new assertions of existence of the calculus. The unit route
and target signatures remain unchanged.

Checked edge cases: length zero; empty and regular inputs; a singleton value set with
no positive labels; one extension; arbitrary non-well-founded value orders; lower cuts
with no active label or all active labels; active intrinsic identity blowups; common
stage zero; two unequal lengths with one regular endpoint. The latter cannot both be
terminal first-regular realizations, by the explicit two-direction contradiction.
Existing FiniteMaximumLabeledHistory only packages stronger supplied data and gives no
constructor of the missing tower. The intrinsic-cocycle theorem requires that stronger
cut data and its DAG route passes through finite realization via smooth deletion; it
cannot supply this construction or justify a circular proof of stopping uniqueness.

## New nodes

lem-trf-maximum-history-chronology attaches the proved finite chronological history
existence theorem and its two genuine partial-data structures. Its proof records the
finite-tuple construction, dependent recursion, calculus geometry and label progress.

lem-trf-maximum-history-lower-cut-tower isolates the reindexing and padding of a supplied
finite stopped chronology. It supplies none of the chronology, its termination, or its
length uniqueness. Its data structure retains every center and all initial equations.

lem-trf-maximum-history-common-stage isolates the geometric common-prefix comparison
needed for stopping uniqueness. It assumes no final regularity and asserts only the
regularity equivalence at a specified common stage, not the full unique diagram
comparison of the item.

All new nodes record actual LeanSearch, Lean Finder/Loogle and Mathlib grep searches,
with verdicts, plus source places, full proof steps and matching Lean statements.
No change record is needed: no existing definition, statement or public interface was
altered, and no other existing module or node was adapted.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
