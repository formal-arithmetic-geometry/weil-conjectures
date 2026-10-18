## What changed

Proved `AlgebraicGeometry.ProEtale.finiteLevelAmplification_consequences` in
`Sheaf.AlgebraicGeometry.AmplificationConsequences` without changing its signature.
Added the proof-only import `Sheaf.Paper.RestrictionDirectImage`. Extracted both FIN
hypotheses and both pullback hypotheses from AMP at the selected positive quotient.
Applied `restrictionDirectImage` to both FIN hypotheses, bundled each ambient object
with its constructibility proof, and paired the resulting constructibility and
interval statements. Paired the corresponding AMP clauses for both pullbacks.
Identified the arbitrary discrete topology with the canonical one using
`DiscreteTopology.eq_bot`. Updated the node proof and dependencies to match.
The server compiled the completed proof successfully (4.0 seconds, no diagnostics).

Searches: LeanFinder for finite-level amplification and preservation of bounded
constructible intervals found only general derived-category and site results;
Loogle found `DiscreteTopology.eq_bot`; msearch grep for
`restrictionDirectImage|finiteCoefficientPullbackAmplifies` found no extra result.
Reading and rg searches of the project supplied the existing restriction theorem
and AMP definitions. The unit's statement and three proof steps are unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.finiteLevelAmplification_consequences`
(node `prop-weil-pbc-amplification-consequences`).
Added zero holes. No `sorry` remains in the delivered Lean module; no split-offs.
The proof uses the existing `restrictionDirectImage` theorem, whose own outstanding
proof remains the responsibility of its existing node; no dependency is restated.

## No longer needed

The proof does not need node
`lem-weil-pbc-pullback-preserves-bounded-constructible` or its module
`Sheaf.AlgebraicGeometry.PullbackBoundedConstructible`: AMP already includes the
required constructibility and interval clauses for both pullbacks. Removed that
node from this item's proof dependencies. The module was not imported originally,
so no existing import was removed. All remaining imports are used.
This is pruning of this proof dependency only; other parents may still use it.

## Where the brief, the DAG or earlier work was wrong

The planned appeal to the general pullback restriction theorem is redundant once
AMP is assumed. Its separate complete-coefficient-datum interface is unnecessary
here. The original theorem and its assumptions are unchanged. No definition or
statement repair, forced adaptation, or change record is needed.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
