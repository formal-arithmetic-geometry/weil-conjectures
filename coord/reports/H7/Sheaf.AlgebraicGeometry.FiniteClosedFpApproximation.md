## What changed

Proved `AlgebraicGeometry.exists_finite_closed_fp_approximation` in
`Sheaf.AlgebraicGeometry.FiniteClosedFpApproximation`, without changing its signature,
visibility, or docstring. Added proof-only imports of
`Mathlib.CategoryTheory.Limits.Final` and `Mathlib.CategoryTheory.Whiskering`.

Finite-morphism permanence first supplies qcqs for the source. The existing theorem
`exists_locallyFiniteType_limit_closed_finitePresentation` supplies the directed system.
Its qcqs stage properties, finite-presentation structure maps, and closed transitions
supply all instances required by `eventually_finite`. Restricting to the upper tail
above its index gives finite stages. The tail is explicitly nonempty and directed;
its opposite inclusion is initial by `Functor.initial_of_exists_of_isCofiltered`.
`Functor.Initial.isLimitWhiskerEquiv` transfers the original limit to the tail.
Whiskering the structure and projection transformations preserves every remaining
clause definitionally.

The Lean proof follows all three existing DAG proof steps, so no node changes are
necessary. Read the source proof in Stacks `limits.tex`,
`lemma-finite-in-finite-and-finite-presentation` (Tag 09YY). The unit route stays intact.
The singleton tail case and an empty base require no additional assumptions: the
chosen index itself inhabits the tail, and no scheme point is chosen.

Validation: the complete module compiled without errors or warnings through
`lcompile.py` in 2.7 seconds of compiler time. Both existing Sheaf proof imports pass
`tools/import_direction.py may`. LeanFinder and library/Mathlib searches found no
shorter theorem with the required closed transitions; the existing two declared
proof dependencies fit directly.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.exists_finite_closed_fp_approximation`
(node `lem-weil-pbc-finite-closed-fp-approximation`).

Zero holes remain in the assigned module. Zero holes added; zero split-offs.
The existing imported declarations
`AlgebraicGeometry.exists_locallyFiniteType_limit_closed_finitePresentation` and
`AlgebraicGeometry.eventually_finite` retain their own pre-existing holes; this
proof uses their stated interfaces as the stage-3 brief requires.

## No longer needed

None. No imports removed and no nodes or modules pruned. The proof uses the planned
finite-type approximation and eventual-finiteness dependencies, together with the
listed Mathlib permanence facts. Cofinal-tail restriction uses Mathlib's generic
initial-functor limit equivalence instead of reconstructing the same universal
property by hand; this is the elementary third step of the existing plan.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface defects found. The stated proof plan works with the
existing declarations and needs no repairs or new nodes.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
