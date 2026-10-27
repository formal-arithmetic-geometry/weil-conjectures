## What changed

Proved `AlgebraicGeometry.Scheme.Modules.gradedLineFraction_test_local` in
`Sheaf.TraceFormula.GradedLineFractionTestLocal`, preserving its signature and public imports.
Added proof-only imports of `GradedLineFractionSameBase` and `LineProjChartPullback`
using `import all` to reuse their already proved private coefficient, fraction and
pullback-power lemmas. All new helpers in the item are private and fully proved.
The proof descends the test trivialization through the restriction adjunction,
identifies the homogeneous coefficients, and compares localization charts with
the natural `Proj.fromOfGlobalSections` map. Updated the item's DAG proof accordingly.
No shared definitions, source-library declarations, or consumer interfaces changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.gradedLineFraction_test_local`
(node `lem-trf-graded-line-fraction-test-local`).
Added no holes and split off no statements. Zero textual `sorry` remain in the item.

## No longer needed

No original imports removed and no modules withdrawn.
The planned dependency `lem-weil-pbc-scheme-morphism-gluing` is unnecessary:
this theorem is local, and the chosen open immersion's range isomorphism gives
its neighbourhood equality directly. Removed that node from this item's proof dependencies.
All other original mathematical ingredients remain in the proof, with existing
proved helper modules supplying the coefficient and pullback calculations.

## Where the brief, the DAG or earlier work was wrong

The statement and source argument are correct. The original one-step DAG plan
omitted the explicit descent of a frame from the open test to its image, but this
follows from uniqueness of the restriction and tensor-pullback adjunctions.
Global invertibility of L is not needed: the supplied test trivialization suffices.
Empty tests are vacuous, and localization and unit-ideal arguments also handle
nilpotent denominators and the zero ring. No additional assumptions were introduced.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
