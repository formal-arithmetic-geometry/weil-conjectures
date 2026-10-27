## What changed

In `Sheaf.Paper.CompletedPrimitiveCounitComparison`, prove the five preliminary
geometric-system declarations using the definitionally identical interface in
`Sheaf.Paper.IntegralComparisonSequenceSystems`, plus direct unfolding for `section_eq`.
This follows the stage-2 review's N1 advice to reuse that interface.

Name the existing Roos comparison type, projection predicate and resolution predicate
so that generated record declarations keep the long formulas folded. All three record
fields are definitionally the old fields. Use explicit local unfolding and functor
arguments for the two existing bridge definitions, and local transparency/instance
settings for the long model predicates. No mathematical statement is changed.

Change record: `coord/changes/S3-completed-primitive-roos-predicates.md`.
The node now records the reused dependency and the three predicate declarations.

## Proved and sorry left

Closed 5 of the original 8 holes, with 0 holes added and 0 split off:

- `WeilConjectures.PrimitiveCounit.base_continuous`, by
  `integralComparisonSequenceBaseChange_continuous`.
- `WeilConjectures.PrimitiveCounit.section_eq`, by unfolding and reflexivity.
- `WeilConjectures.PrimitiveCounit.ringMap_natural`, by
  `integralComparisonSequenceRing_naturality`.
- `WeilConjectures.PrimitiveCounit.direct_isRightAdjoint`, by
  `integralComparisonSequenceDirectImage_isRightAdjoint`.
- `WeilConjectures.PrimitiveCounit.inverse_exact`, by
  `integralComparisonSequencePullback_exact`.

The last dependency still has an existing sorry in its own module. This delivery
closes the item's duplicate exactness hole from the stated dependency, as stage 3
permits; it does not claim to prove that dependency from Mathlib.

The following 3 original holes remain unchanged, all attached to
`lem-pur-completed-primitive-counit-comparison`:

- `WeilConjectures.PrimitiveCounit.directEvaluation_eq`.
- `WeilConjectures.PrimitiveCounit.inverseEvaluation_existsUnique`.
- `WeilConjectures.completedPrimitiveCounitComparison`.

This is a partial multi-hole delivery, not a decomposition of the main theorem.
No axiom or holed definition is added. The original uniquely unit-normalized
inverse-evaluation existence theorem continues to determine its chosen comparison.

Validation: the full item compiles (latest batch reports 45.4 seconds).
The unchanged consumers `CompletedUnitPullbackTower`,
`ExpressionCounitSubstitutionCoherence` and `FiniteExpressionReductionComparison`
also compile against the changed item. The latter batch completed successfully;
its earlier timeout was not a type error. All consumer sources were byte-identical
to the library and are not part of the delivery. The two transport consumers are
also checked in a batch that includes the item source.

## No longer needed

Remove these five private imports from the item:

- `Sheaf.Paper.NormalizedDVREffectivity`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.

They are unused by the five proofs and all retained definition bodies compile without
them. No node or module is withdrawn: the main theorem is still unfinished, and its
stated proof plan still needs the quotient-system, Roos-descent, effectivity and
resolution dependencies. Their DAG dependencies and approved tool uses are retained.

## Where the brief, the DAG or earlier work was wrong

The stage-2 review already identified the duplicate system interface. Its constructions
are definitionally the same as this item's base, ring component, direct image and
chosen left adjoint, so the corresponding existing declarations apply directly.

The direct-evaluation ring-map square can be checked sectionwise, but converting the
result to equality of the two composed module-pushforward functors caused extensive
unfolding. The exploratory proof was not retained. The inverse-evaluation uniqueness
and main quotient/Roos realization arguments remain in their original named theorems.
No statement is disputed and no target or unit route has been changed.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
