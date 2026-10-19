## What changed

Proved `AlgebraicGeometry.ProEtale.constantModelBoundedConstructible_field_triangulated` in
`Sheaf.Paper.CoefficientHeartTriangulated`, with its signature and public imports unchanged.
Retained the proof import of `Sheaf.Paper.CoefficientHeartClosure` and added
`Sheaf.Paper.CohomologyInWeakSerreSubcategory` and
`Mathlib.CategoryTheory.ObjectProperty.Retract`. Updated the existing DAG node to this route.

The coefficient-heart theorem supplies kernel, cokernel and extension closure, together
with an abelian full subcategory whose zero object gives constructible zero. The first
well-definedness clause supplies isomorphism closure. The existing proved weak Serre
cohomology theorem and canonical boundedness give triangulation. A private proved helper
constructs any retract as the kernel of the complementary idempotent, and the same
cohomological bounds descend along retracts. Specialization gives exactly the two stated
coefficient choices, including the empty-scheme and rank-zero cases.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.constantModelBoundedConstructible_field_triangulated`
(node `det-cor-coefficient-heart-ii-triangulated`). No holes remain in the item; no holes
were added or split off. Both private helpers are completely proved.

This is a proof from existing stated dependencies, not a claim that every dependency is
already sorry-free. It still uses `coefficientHeart_closure` and the isomorphism clause of
`constantModelConstructibleFiniteTor_wellDefined`, which remain their existing items.

## No longer needed

Removed the direct imports `Sheaf.CategoryTheory.RingedSiteModules`,
`Sheaf.Paper.PbcQbarStandardCohomology`,
`Sheaf.Paper.SfCommonStageWeilCohomology`,
`Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`,
`Mathlib.CategoryTheory.Shift.ShiftSequence`,
`Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
`Mathlib.CategoryTheory.Abelian.Basic`,
`Mathlib.CategoryTheory.Triangulated.Pretriangulated`, and
`Mathlib.Algebra.Homology.DerivedCategory.Basic`.
The generic homology-property theorem provides the shift and exact-sequence infrastructure.
The coefficient closure theorem supplies zero, so no explicit scalar local-model construction
is needed here. The common-stage Weil and Pbc cohomology constructions concern different
categories and are unused by this ambient-derived-category proof.

The old direct proof dependencies `def-weil-size-convention`,
`def-weil-sheaf-of-modules-category`, `def-weil-derived-cohomology-sheaves`,
`det-def-sfb-constructible-local-model`, `lem-sp-derived-cohomology-shift`,
`lem-sf-derived-homology-long-exact`, `lem-weil-pbc-coimage-mono`, and
`def-weil-triangulated-category` are no longer direct dependencies. Some remain dependencies
of the existing generic argument or coefficient-heart theorem; no global unreachability is
claimed. The unit's cone argument is retained through the existing weak-Serre proof.

## Where the brief, the DAG or earlier work was wrong

The inherited proof compiled cleanly in 3.9 seconds against the current published build.
The earlier 900-second failure was in delivery preflight, not a reproduced Lean timeout;
there is no evidence warranting a definition change. The fresh required dry run completed
and identified an added global `open CategoryTheory Limits ZeroObject` as an interface
change without a change record. Restored the original `open CategoryTheory`; all needed
limit names are explicit in the proof. Replaced the scoped zero-object numeral by
`Limits.HasZeroObject.zero`, avoiding the extra scoped instances entirely. The repaired
file compiled cleanly in 4.3 seconds; the interface comparison is empty. No statement or
definition is changed.

On resuming this sandbox, rechecked the preserved proof against the current sources.
The server compiled it cleanly in 4.0 seconds. The required fresh `deliver3.py --no-push`
completed successfully, including its axiom probe and preflight, with review class CODEX
because the proof route updates the existing node. The static comparison confirms no
changed statement, no changed public interface, one original hole closed and zero added.
Thus the reported slow-definition failure is not reproduced; no definition repair is
needed for this compiling delivery.

The requested `IsNoetherian X` does not synthesize from the separate hypotheses
automatically; the proof constructs it from the existing locally Noetherian and compact
instances. The common-stage Weil cohomology import in the current source concerns a
different category and is unused by this ambient-derived-category proof.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
