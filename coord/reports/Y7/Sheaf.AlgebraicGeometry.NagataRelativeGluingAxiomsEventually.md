## What changed

Proved `AlgebraicGeometry.nagataRelativeGluingAxiomsEventually` without changing its
signature or `NagataRelativeGluingTransport.HasGluingAxioms`. All proof helpers are
proved private theorems in the assigned module. No new module, axiom, definition
repair, or intermediate hole is delivered.

Every selected relation stage is below the common finite upper bound. The two
existing eventual-equality theorems therefore prove every recorded relation at
that bound. Finite-list membership selects each gluing equation. Pullback
comparison isomorphisms and an explicit outer lift transport intersection and
triple equations. Backward domain matching follows by pulling forward domain
matching back along the backward map and using the inverse identity.

Added proof imports for Mathlib pullback preservation and connected limits in
Over categories. Updated the existing node's proof and proof dependencies to
match this implementation. The consolidated module passed remote single-file compilation without warnings
in 11.9 seconds. The delivery dry run performs the final integration checks.

The shorter-route search used LeanFinder for transport of pullback equations
(finding `PreservesPullback.iso` and its projection API), Loogle for
`CategoryTheory.Over.pullback` (finding the pullback adjunction and functor), and
grep for `PreservesPullback.iso_inv_(fst|snd)` and connected Over limits. Local
search of both project roots found no existing assembly theorem.

## Proved and sorry left

Closed: `AlgebraicGeometry.nagataRelativeGluingAxiomsEventually`
(node `lemma-nagata-relative-gluing-axioms-eventually`), the module's sole original hole.
Added: none. Remaining in delivered Lean files: none. Thus 1 of 1 original sorries
is proved, with 0 split off. The existing imported eventual-equality and
upper-bound declarations are used as intended by stage 3.

## No longer needed

Removed the direct proof imports `Sheaf.AlgebraicGeometry.RelativeFiniteAffinePresentation`
and `Sheaf.AlgebraicGeometry.NagataRelativeGluingDatumDescends`.
The node's proof no longer needs `def-nagata-relative-finite-affine-presentation`
as a separate proof dependency, or `lemma-nagata-relative-gluing-datum-descends`:
the valid-stage choices already retain the required limit equations and finite
presentation inputs. The presentation's definitions remain available through the
public valid-stage import. No claim is made that these nodes are unused by every
other target branch.

The orientation-cover argument for backward domains is unnecessary: the inverse
identity and forward domain equality suffice. The unit's statement and route are
unchanged. No other modules or nodes are pruned by this delivery.

## Where the brief, the DAG or earlier work was wrong

The existing plan redundantly re-establishes limit equations from the raw datum
comparison even though the equality-choice records already supply them. It also
uses a longer cover argument for backward domain matching. Neither issue changes
the mathematical statement; the node now records the shorter implementation.
The original theorem docstring is retained as the prior proof plan.

Empty chart and overlap index types need no special assumption: the proof selects
relations only for supplied indices, and preserves arbitrary unions. The finite
upper-bound proof uses the fixed pair-bound law, not an assumed linear indexing
order. No data is selected from an unproved existence theorem.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
