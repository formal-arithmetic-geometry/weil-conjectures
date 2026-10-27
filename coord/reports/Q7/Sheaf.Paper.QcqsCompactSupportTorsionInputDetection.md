## What changed

Marked `WeilConjectures.sfQcqsCompactSupport_torsion_input_ext` as
`STATEMENT-DISPUTED`, with the exact missing premise of its proposed proof recorded
beside the declaration and in its node. Its signature and existing hole are unchanged.

Added `Sheaf.Paper.QcqsCompactSupportNormalizedIsoExistence`, proving
`WeilConjectures.sfQcqsCompactSupport_normalizedIso_exists`: the two compact-support
functors admit a natural isomorphism with every prescribed finite projection equation.
This uses the existing strict comparison and finite comparison declarations, then a
complete-cone argument. It uses neither torsion-input detection nor reduction rigidity.
The proof has no new holes. This is a proposition asserting existence; it does not
introduce a definition choosing arbitrary data from an unproved existence theorem.

Refactored the unclaimed parent `Sheaf.Paper.QcqsCompactSupportNormalizedLift` to use
the hom of this isomorphism for its existence part. Its public signatures and its
uniqueness argument are unchanged. Its node now names the actual dependency. The
change record is `coord/changes/q7-qcqs-normalized-existence.md`.

The new module compiled cleanly in 6.5 seconds. The changed parent and its unchanged
direct consumer `QcqsCompactSupportRealization` compiled cleanly against the same
sandbox (51.6 and 55.9 seconds). The unchanged consumer copy was then removed.
The combined check also compiled the new module in 53.7 seconds.
No source-library declaration, target statement or definition was changed.

## Proved and sorry left

Assigned holes closed: **0 of 1**. Holes added: **0**. This packet does not claim a
reduction or proof of the disputed rigidity theorem, nor a net sorry-ledger improvement.

The one remaining hole is
`WeilConjectures.sfQcqsCompactSupport_torsion_input_ext`
(node `lem-qcqs-compact-support-torsion-input-detection`).

The added theorem `WeilConjectures.sfQcqsCompactSupport_normalizedIso_exists` is
proved from the existing declarations; all four private helpers are proved. Like
other stage-3 proofs it still depends on pre-existing holed geometric declarations,
including `qcqsCompactSupport_strictReductionData` and
`qcqsCompactSupport_strictReductionGamma`; these are not new holes of this packet.
The parent remains proved from its recorded dependencies, including the disputed hole.

## No longer needed

Removed the parent's private import of
`Sheaf.Paper.QcqsCompactSupportStrictReductionComparison` and its duplicate private
`projection_transpose` proof. The strict comparison is now used by the new existence
module. Therefore **no module or DAG dependency is globally pruned**: the strict
comparison is still needed transitively, and rigidity remains needed for uniqueness.

No dependencies of the assigned theorem are declared obsolete. In particular, zero
current importers or absence of a short proof is not used to withdraw its node. The
unit `sk-def-sf-operations` has no realized step bypassed by this change.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: The assigned node's sole proof step asserts that agreement on
finite torsion inputs identifies universal counit comparisons on a simultaneous strict
resolving category. Its Lean hypotheses are **arbitrary ordinary natural
transformations on derived categories**. They contain no strict or enhanced lift, nor
any compatibility with those resolving diagrams. The cited declarations construct
particular strict towers and their particular comparisons. They do not lift an
arbitrary transformation to that construction. Naturality alone gives equality after
composition with the finite augmentation maps; the proposed proof needs equality of
whole derived-system maps before applying the adjunction. These are different claims.

This is a missing mathematical argument, not a compiler failure and not an objection
to using existing `sorry` declarations. Every cited declaration and its signature was
read. The reduction/limit adjunction and `integralSystemReduction_fullyFaithful` detect
whole system maps. Finite evaluations detect isomorphisms, which suffices for the added
existence theorem; their conservativity does not establish equality of maps. The
available Milnor injectivity proofs use finite shifted Hom groups over
`FiniteFieldDatum.k`, whereas the assigned theorem quantifies over an arbitrary base
field. Specializing that field or adding enhancement hypotheses would change the
assigned statement, so neither change is made.

The cited sources do not state the assigned assertion. Stacks 0941,
`sites-cohomology.tex`, `lemma-derived-limit-is-ok`, compares the total derived limit
of a given strict system with its evaluated homotopy limit. Stacks 0F7J,
`more-etale.tex`, `lemma-shriek-composition`, constructs compact-support composition.
Bhatt--Scholze 6.7.6--6.7.7 construct compact support and its independence. The current
blueprint's scalar-six compact-support proof characterizes its **particular refinement
maps** using the open adjunction. It does not assert uniqueness of all ordinary natural
transformations from their values on torsion inputs.

No counterexample to the assigned theorem is claimed. Independent review should
resolve this distinction before the same obligation is split again. A safe path for
the parent construction would be to construct its comparison data explicitly and
prove their required coherence, without using arbitrary-transformation uniqueness;
this packet only establishes the existence proposition needed for such a path. It
does not replace the canonical realization definition by a choice from this proposition.

## New nodes

`lem-qcqs-compact-support-normalized-iso-existence` matches
`Sheaf.Paper.QcqsCompactSupportNormalizedIsoExistence` and its public theorem. It is
the existence and invertibility portion of the already used normalized realization,
with no uniqueness assertion. Its proof is completely written in Lean. Mathlib
searches found componentwise invertibility API, used in the proof, but no geometric
existence result; blueprint searches for compact-support realization found no matching
standalone node. The current blueprint scalar-six proof's Isomorphism paragraph and
the existing normalized-lift and realization nodes locate the construction. The
parent consumes this new node. No new `sorry` statement is split off.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
