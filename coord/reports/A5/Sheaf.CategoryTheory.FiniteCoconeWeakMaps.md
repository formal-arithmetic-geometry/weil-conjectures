## What changed

Proved `CategoryTheory.BigradedExactCouple.finiteCocone_weakMaps` with its original
signature, following the existing node's four-step proof plan. Extracted the two
tail hypotheses and applied `finiteCocone_limitCycles` and
`finiteCocone_limitBoundaries`. The cycle image equality makes the canonical
factorization of initialG epic; the graded map is epic by image factorization.
The existing quotient-kernel and image-pullback helpers compute the two kernels
as the same supremum, in opposite orders. Explicit inverse integer-index
transports relate the incoming diagonal alpha image to the initialG kernel and
identify its cocone image with the next filtration step.

The proof uses the declared dependencies as statements; it does not unfold the
recursive tower. No definitions, public signatures or public imports changed.
The existing DAG plan and proof dependencies remain accurate.

Validation: the final module compiles through `lcompile.py` without warnings
in 3.2 seconds. The delivery dry run additionally checks declarations and axioms.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.BigradedExactCouple.finiteCocone_weakMaps`
(node `lem-sp-finite-cocone-weak-maps`).

Holes closed: 1 of 1. Holes added: 0. No sorry remains in the delivered module.
The imported stationary-cycle theorem remains a separate existing obligation;
this delivery proves the assigned theorem from that stated dependency, as required.

## No longer needed

Removed the redundant proof imports `WeilConjectures.CategoryTheory.ExactCouple`
and `WeilConjectures.CategoryTheory.ExactCoupleConvergence`; both remain available
through the unchanged public import
`Sheaf.CategoryTheory.ExactCoupleConvergence`. No dependency node or module is
pruned from the mathematical route: both finite limiting-subobject formulas,
abelian refinement calculus and the exact-couple/convergence definitions are used.
No new modules or nodes were introduced.

## Where the brief, the DAG or earlier work was wrong

None. The stated dependencies give the required formulas. The integer-index
transports in the canonical maps require naturality rather than direct dependent
rewriting; this is handled explicitly in the proof.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
