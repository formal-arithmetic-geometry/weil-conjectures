## What changed

Completed all five theorem holes in Sheaf.Paper.LocalFrobeniusTrace, following
the existing four-step DAG proof. The two compatibility equations use Spec
composition and the prescribed embedding equations. Closed-point degree
positivity uses closedPoint_iff_residueField_trdeg_zero_and_finite and
Module.finrank_pos. The return equations use the existing proved
FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_of_card_eq,
together with three fully proved private helpers for positive powers,
Frobenius projection equations, and pullback uniqueness.

Added the private proof import WeilConjectures.PointCount for
Scheme.Hom.specMap_residueFieldAlgebraMap. All original public signatures,
public imports, definition bodies, and docstrings are preserved. Scoped the
transparency option to the private pullback helpers and the unused-section-variable
linter to localClosedPoint_compatible. These local elaboration changes and every
transitive consumer are documented in
coord/changes/Z5-local-frobenius-trace-elaboration.md; no consumer adaptation is needed.
Updated only the definition node's proof-origin attribution; its recorded route
already describes the proof now implemented. No unit route is bypassed.

The shorter-route searches used leanfinder, loogle, and grep through msearch.py,
plus direct searches of both library roots. Loogle found Module.finrank_pos;
the source library supplies the exact embedded finite-field fixed-point theorem.
No new field theory is necessary.

The complete module compiled through lcompile.py in 14.7 seconds with no errors
or warnings. Source checks verify every original definition body, theorem
signature, and public import is unchanged, zero sorry tokens remain, and all
Lean lines are at most 100 characters.

## Proved and sorry left

Closed five original holes, all attached to def-weil-local-frobenius-trace:

- WeilConjectures.localExtensionPoint_compatible.
- WeilConjectures.localExtensionPoint_return.
- WeilConjectures.localClosedPointDegree_pos.
- WeilConjectures.localClosedPoint_compatible.
- WeilConjectures.localClosedPoint_return.

Zero holes remain in the item, zero holes are added, and zero statements are
split off. The three new private helpers are proved in full.

## No longer needed

None. No existing import, declaration, module, or node is removed. Every
recorded proof dependency remains in use. The existing fixed-field theorem
avoids introducing any new statements or dependencies.

## Where the brief, the DAG or earlier work was wrong

The node and A8 report record an earlier completion, but the current source
still contains all five holes. The ledger records the earlier delivery's
return after a global-build failure. This packet completes the actual current
source; it is not a rebase or a compiling no-op. No mathematical statement or
definition repair is needed.

The positive-power convention is exponent n+1. In particular, n=1 and residue
degree r=1 use the zero index, and positivity justifies subtraction in both
return proofs. The return equation is semilinear reparametrization, exactly
as stated; it does not assert literal fixedness of the geometric point.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
