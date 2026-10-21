## What changed

Filled `AlgebraicGeometry.ProEtale.constructible_exact_scalar_triangulation` in
`Sheaf.AlgebraicGeometry.ConstructibleExactScalarTriangulation`. The finite-field Serre
closure theorem gives the three ObjectProperty closure instances; kernel and cokernel
closure are transported from the chosen limits to arbitrary limiting cones using
constructibility under isomorphism. The proved conditional bounded-constructible
triangulation theorem supplies the triangulated subcategory, additive shifts and inclusion.
Ordinary scalar extension uses the existing additive, flatness and colimit instances.
The recorded shift structure is transport along the inverse of the unchanged canonical
comparison: Mathlib's `CommShift.ofIso_compatibility` and inverse compatibility give the
forward comparison, and `Functor.isTriangulated_of_iso` transfers exact termwise
triangulatedness. Composition and left whiskering give the last two clauses.

Added proof imports of `WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed` and
`Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`.
Updated the item's DAG proof to this argument. The public-import change is recorded in
`coord/changes/constructible-exact-scalar-public-imports.md`; `tools/downstream.py` reports
zero downstream modules, and the live/quarantined Lean search finds no importers. No declaration signature, definition body,
or source-library file changed. The unit's finite-field descent route is preserved; the
conditional triangulation theorem is a proved generic tool replacing the same generic
weak Serre assembly. No additional assumptions such as qcqs or completeness were used.

Validation: single-file server compilation passed without errors or warnings in 15.1 s.
Checked the existing theorem signature and canonical comparison definition against the
original text: both are unchanged. No new axiom, new theorem, or data construction was
introduced. The identity/zero stratum cases are covered by the existing conditional
triangulation proof; the shift transport is uniform over all integers.

## Proved and sorry left

Closed one of one holes:
`AlgebraicGeometry.ProEtale.constructible_exact_scalar_triangulation`
(node `lem-sfb-constructible-exact-scalar-triangulation`). Added zero holes; split off zero
statements. No sorry remains in the delivered module. Existing imported obligations,
including the coefficient flatness instance, are retained as named dependencies; this
packet proves the assigned theorem from those declarations and does not claim their
transitive axiom closure is finished.

## No longer needed

Removed proof imports `Sheaf.Paper.CohomologyInWeakSerreSubcategory` and
`Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`. The first is replaced by the proved
conditional triangulation API; the second is unnecessary because the existing canonical
comparison already identifies the recorded total left derived functor with the termwise
one. The generic weak Serre mathematics remains used inside the conditional API.

Removed unused public imports `Sheaf.AlgebraicGeometry.ProEtalePointPullback`,
`Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale` and
`Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensorExact`. Their specialized
interfaces do not occur in any signature or proof here: the statement uses the original
internal-module boundedConstructible predicate, and the comparison uses the upstream
leftDerivedFunctor interface rather than leftDerivedFunctorFromTotalTensor. In particular,
the unused discrete coefficient-sized site interface and alternative total-tensor API
are not needed by this proof. No module is withdrawn and no upstream declaration is
removed. Retained the public imports of the actual derived coefficient functors and the
recorded shift structures.

The proof no longer directly needs nodes
`lem-sfb-condensed-coefficient-presentation-identification`,
`lem-sbc-cohomology-in-weak-serre-subcategory`, and
`lem-weil-pbc-exact-functor-derived-functor`. The first is unnecessary because the finite
Serre theorem already states exactly the live coefficient and constructibility predicate;
the other two arguments are already packaged in the existing proved APIs. Removed the
obsolete top-level tool approvals for the latter two from this node, retaining the other
approvals in order. Statement dependencies remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The upstream noetherian-only arbitrary-ring triangulation instance is marked disputed
and is not the justification used here. Explicitly constructing closure instances and
calling the proved conditional theorem avoids using it for the first conclusion.
The original plan reconstructed a canonical comparison that the assigned module already
constructs. Its recorded shift structure is exactly `CommShift.ofIso` of the inverse of
that comparison, so compatibility and triangulatedness can be transferred directly.
The existing finite-field Serre theorem already uses the exact coefficient object and
stratified local-presentation predicate; a separate presentation-identification theorem
is not needed. No mathematical statement was changed.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
