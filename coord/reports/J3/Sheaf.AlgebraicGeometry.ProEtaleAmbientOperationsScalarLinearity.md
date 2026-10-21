## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleRingDerivedOperations_scalarLinearity` in
`Sheaf.AlgebraicGeometry.ProEtaleAmbientOperationsScalarLinearity`, with its signature
unchanged. A proved private abbreviation constructs the Hom-module structures by
restricting `SheafOfModules.homLinear` along the specified section ring maps. Their
sectionwise formulas hold definitionally. Direct-image linearity follows sectionwise
from `hc`; the source-library adjunction lemmas give underived pullback linearity and
derived direct-image linearity, with Mathlib exact derived-functor linearity between them.
The private proof import
`WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor` supplies those two existing
adjunction calculations. All four steps of the existing DAG proof are followed, so no
node update or interface change is needed.

The module compiled through `lcompile.py` without errors or warnings (3.8 seconds).

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.proEtaleRingDerivedOperations_scalarLinearity`
(node `lem-sbc-ambient-operations-scalar-linearity`).
One of one original sorries proved; zero holes added, zero split off, zero remaining
sorries in the delivered module. The private `sectionScalarLinear` construction is
complete and contains no postponed proof or arbitrary witness selection.

## No longer needed

None. No imports, nodes, or modules are pruned. The source-library adjunction lemmas
encapsulate exactly the unit and counit calculations in steps 2 and 4; they do not
replace the node's route. All existing proof dependencies remain used.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. Existing source-library
`CategoryTheory.Adjunction.left_adjoint_linear` and `right_adjoint_linear` already
provide the two generic adjunction arguments. The unit `sk-rem-rest` has no specified
realized steps, and the node's four-step route is preserved.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
