## What changed

Repair of returned head `1e2d2af4a3f` (reviewer C-1e2d2): the mathematics passed
review, but landing rejected the reviewer override's filename. The record was
present in the delivery at `coord/changes/U4-quotient-coherence-reduction.md`.
Inspection of `tools/batch_land.py`, function `fixes`, identifies the required
override name as `U4-quotient-coherence-reduction.change.md` (record stem plus
`.change.md`). The record header now states this exact mapping so a subsequent
review can apply any corrections with the accepted filename. The repository
record itself keeps its `.md` name. No launcher or project tool is modified.

The existing node has been refreshed from current sheaf-dag with only the
delivery-owned `lean`, `proof`, `proof_deps` and `proof_origin` fields reapplied.
All six new nodes remain absent from the current source. Lean statements and
proofs are retained from the passed delivery. Fresh server validation follows.

Repaired the retained proof of `WeilConjectures.integralQuotientMixedCoherence`.
The twelve unchanged clauses are assembled from ordinary scalar-generator
interchange, geometric adjunction-mate associativity and units, exact-derived
unit compatibility, and five independent component statements.

The shared scalar comparison constructions and bracketing API now live in
`Sheaf.Paper.QuotientSystemMixedCoherenceData`, publicly re-exported by the item.
This allows the new component modules to import their definitions without an
import cycle. The original public names and signatures are retained. Bracketing
recursion is explicitly structural. The twelve structure field types are literal
copies factored through named clause definitions. No source-library or Challenge
file changes. See `coord/changes/U4-quotient-coherence-reduction.md`.

## Proved and sorry left

Closed the original body of `WeilConjectures.integralQuotientMixedCoherence` by
assembly from smaller statements. This is a decomposition, not a claim that its
axiom closure is sorry-free. The two original scalar existence/uniqueness
proofs remain proved. The item module has zero holes; five holes are added:

- `WeilConjectures.sequenceDerivedCoherence`:
  `lem-trf-sequence-derived-associativity`, module `SequenceDerivedAssociativity`.
- `WeilConjectures.sequenceFiniteCoherence`:
  `lem-trf-sequence-finite-bracketing-coherence`, module `SequenceFiniteBracketingCoherence`.
- `WeilConjectures.sequenceDerivedMixed`:
  `lem-trf-sequence-derived-mixed-square`, module `SequenceDerivedMixedSquare`.
- `WeilConjectures.sequenceDerivedScalarUnit`:
  `lem-trf-sequence-derived-scalar-unit`, module `SequenceDerivedScalarUnit`.
- `WeilConjectures.sequenceDerivedScalarTower`:
  `lem-trf-sequence-derived-scalar-tower`, module `SequenceDerivedScalarTower`.

Each split is public, has exactly `:= by sorry`, its complete source proof in
words, and its own module and DAG node. The finite result is generic in the
category and used twice; the four derived equations each establish only one
component of the twelve-clause result. Empty paths, singleton paths, identity
arrows, equal coefficient fields, and nonflat scalar extensions are included.
All seven delivery modules compiled successfully through lcompile.py --all.
The item and data module contain zero holes; each of the five component modules
contains exactly one. A literal comparison confirmed that all twelve factored
field propositions match their original types modulo whitespace. Delivery
preflight initially found a mismatched metadata signature; it has been corrected.
The three scalar-comparison consumers flagged by preflight are now included
in the change record, with unchanged public re-export and no forced edits.

## No longer needed

The completed assembly does not import the planned generic
`Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent`. Its node remains a
proof dependency of the four derived split steps where appropriate, so no
withdrawal or global pruning of that module is claimed. The abandoned private
normalized-model development and unfinished finite-path proofs are retained
only in the sandbox scratchpad, outside the delivery.

No existing library declaration or module is withdrawn. No original public
import is lost: the data module re-exports the same statement dependencies.
The ambient tensor and independent change-of-rings proof imports are not needed
by the completed main assembly; independent change of rings remains used by
the shared scalar-comparison existence proof in the data module.

## Where the brief, the DAG or earlier work was wrong

The retained attempt was not compiler validated. Its finite-path transport
identifications and the derived model normalizations had unresolved Lean goals;
these have been replaced by explicit independent component statements rather
than claimed as proved. Its final ordinary associativity assembly also failed
to cancel inverse equality transports, now handled by a proved helper.

No mathematical statement is disputed or weakened. Factoring the twelve exact
field types avoids repeated elaboration of the large structure. The shared data
module is required to make independent component imports acyclic. The data API
move and definition factoring require the normal independent statement review.

## New nodes

`def-trf-quotient-system-coherence-data` records the relocated scalar comparisons
and original scheme-indexed bracketing definitions; it introduces no hole.

`lem-trf-sequence-derived-associativity` is exact-derived preservation of the
ordinary three-arrow equation, with its specific equality transport.

`lem-trf-sequence-finite-bracketing-coherence` reduces arbitrary bracketing
independence to three-arrow associativity and both unit laws, by path induction.

`lem-trf-sequence-derived-mixed-square` is the derived geometric/scalar square,
obtained from its ordinary generator equation on a simultaneous K-flat model.

`lem-trf-sequence-derived-scalar-unit` is the corresponding scalar identity
comparison equation on a K-flat model.

`lem-trf-sequence-derived-scalar-tower` is the scalar tower equation, using
successive scalar extension of the same resolving model.

Change record: `coord/changes/U4-quotient-coherence-reduction.md`.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
