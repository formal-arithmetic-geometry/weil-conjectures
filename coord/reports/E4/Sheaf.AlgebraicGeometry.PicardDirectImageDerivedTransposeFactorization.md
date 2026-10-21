## What changed

Simplified the proved private transpose_three_maps lemma used by
AlgebraicGeometry.Scheme.picardDirectImageDerivedTranspose_factorization.
It now follows directly by rewriting associativity and applying Mathlib's
Adjunction.homEquiv_naturality_left_symm, replacing the explicit congrArg and
equality-transitivity construction. Removed the unnecessary theorem-local
backward.defeqAttrib.useBackward option. The public theorem uses this shorter
categorical proof; its typed coefficientMate_evaluation helper is retained.

The public theorem statement, proof script, docstring, universes, shared derived
category parameter, visibility and all three public imports are unchanged.
No definition, global attribute, source-library module or target meaning
changes. No compile limit or heartbeat budget is increased. The generic
naturality calculation and coefficient mate evaluation include zero modules,
identity maps and empty schemes without inverting a coefficient map.

Rebased the node on the current library record and changed only proof,
proof_deps and proof_origin. Its proof inventory now records the existing
coefficient defining equations and schemeDerivedMate_evaluation actually used.
Change record:
coord/changes/E4-picard-derived-transpose-factorization-restoration.md.

Loogle, LeanFinder and direct Mathlib/library source searches found the
adjunction naturality lemma used in the simplified proof. No duplicate of the
full factorization was found. The source is the one-square base-change mate
construction of Stacks Project Tag 08HY, read in the local Cohomology source.
The unit route is preserved.

Validation: the revised module exported cleanly in 56.6 seconds. A separate
import probe reports only propext, Classical.choice and Quot.sound (11.2 seconds).
The unchanged source control also exported successfully, in 55.4 seconds. The
public signature and imports are byte-identical, the Lean line width is at most
91 characters, and the delivery has zero sorry tokens.

The consumer inventory has one live direct consumer and 17 consumers including
quarantined modules. The unchanged direct consumer,
PicardDirectImageDerivedTransposePasting, reached the 60-second compile limit
against both the revised module and the unchanged exported source control.
This timing issue is present on the control and is reported here for the
maintainer; no compiler type error or changed consumer interface was found.
No consumer adaptation is forced by this proof-only revision.

## Proved and sorry left

The complete proof of
AlgebraicGeometry.Scheme.picardDirectImageDerivedTranspose_factorization
(node lem-sc-picard-direct-image-derived-transpose-factorization) is retained
through the simplified private transpose_three_maps lemma and the proved
coefficientMate_evaluation lemma. Both private helpers are fully proved.

Original holes: 0. Holes closed: 0. Holes added: 0. Sorries left: none.
No theorem is split off. This is a zero-hole proof revision, not a new hole
closure or another copy of the archived restoration.

## No longer needed

The explicit congrArg/trans construction in transpose_three_maps and the
backward.defeqAttrib.useBackward wrapper are no longer needed. Removed
lem-pc-module-pullback-adjunction from the direct proof dependencies; the
argument uses generic adjunction naturality and schemeDerivedMate_evaluation.
That node remains a statement dependency of the coefficient construction.

No module or public import is pruned. All three public imports provide names
in the theorem's statement and remain unchanged. Neither coefficient pasting
nor unit-normalization composition is invoked, but their modules supply the
named coefficient and normalization data. Quarantined consumers retain their
declarations, imports and separate rework obligations.

## Where the brief, the DAG or earlier work was wrong

The returned restoration packet was a no-op: its entire Lean source had already
been restored in the current library, and the current rework table no longer
lists this module. This packet changes an actual proof and its elaboration
configuration and replaces the stale restoration-only report and change record.
The theorem already had zero holes; no new hole closure is claimed.

The current node's proof inventory omits the coefficient defining equations
and base-change mate evaluation required by the current counit presentation.
These existing dependencies are now recorded without changing the mathematical
statement or statement dependencies. No new node or mathematical dispute is
introduced.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
