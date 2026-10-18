## What changed

Proved `AlgebraicGeometry.Scheme.geometricStalk_as_pullback` in
`Sheaf.AlgebraicGeometry.GeometricStalkAsPullback`, without changing its signature.
The sheaf clause is `geometricPoint_pullback_stalk`. For the derived clause, compare
`Sheaf.Γ` with evaluation at the identity étale object, use its equivalence from the
same theorem, and compose the pullback–stalk isomorphism with `uliftSheafFiberIso`.
The exact-functor composition and natural-isomorphism APIs then give the required
unbounded derived isomorphism; exact global sections agree with their right derived functor.

Removed the proof-only import of `Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm`
and added the proof-only import of
`WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic` for `uliftSheafFiberIso`.
The existing DAG plan is realized unchanged: the global-sections equivalence,
pullback–stalk comparison, and exactness pass the sheaf isomorphism to derived categories.

Validation: the module compiled cleanly through `lcompile.py` (4.1 seconds of Lean time).
Searches used Lean Finder, Loogle, msearch grep, and local `rg`; the existing exact-functor
APIs supply the derived-category glue, so no intermediate statement was added.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.geometricStalk_as_pullback`
(node `lem-kun-stalk-as-pullback`). Holes closed: 1 of 1. Holes added: 0.
No `sorry` remains in the delivered module. No split-offs were introduced.

## No longer needed

Removed `import Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm`.
The proof does not need its stronger statement
`AlgebraicGeometry.Etale.isIso_globalGerm_identity`, nor its strictly henselian
sections-to-stalk argument. It uses the original equivalence and pullback–stalk
clauses from `Sheaf.AlgebraicGeometry.GeometricPointPullbackStalk` directly.
No stated dependency node is removed: `lem-weil-pbc-geometric-point-pullback-stalk`
continues to supply those clauses, and exactness of geometric stalks is provided
by the existing Mathlib instances. All public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The `Nonempty` sheaf isomorphism does not require
the additional canonical-germ theorem. The two global-sections implementations
are naturally isomorphic rather than definitionally equal, and the stalk in
the derived clause uses a universe lift; the proof handles both comparisons explicitly.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
