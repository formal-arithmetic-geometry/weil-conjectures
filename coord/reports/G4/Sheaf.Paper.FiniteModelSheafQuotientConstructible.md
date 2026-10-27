## What changed

Replaced the single proof hole of
`AlgebraicGeometry.ProEtale.FiniteModelQuotient.finite_model_sheaf_quotient_constructible`
with a complete Lean assembly from two strictly smaller argument steps.
The main module proves discreteness of the recorded quotient topology from the coset basis,
computes the double complex's kernel and cokernel cohomology under exact constant realization,
proves both scalar modules finite and finitely presented, constructs LocalCalculation,
and derives bounds [-1,0] and both bounded-constructible conclusions.

Moved the coordinate definitions verbatim to FiniteModelSheafQuotientData to avoid an import cycle.
No existing signature or definition body changed. The main module publicly imports that data module.
All four delivered Lean modules compile through lcompile.py; the main module compiles cleanly
with no warnings (11.5 seconds). The moved coordinate block is byte-for-byte identical, and
the main theorem signature matches the original after whitespace normalization.
The source-library boundary is respected; no WeilConjectures file changes.
Change record: coord/changes/G4-finite-model-quotient-coordinates.md.

## Proved and sorry left

Original holes: 1. Closed in the item module:
`AlgebraicGeometry.ProEtale.FiniteModelQuotient.finite_model_sheaf_quotient_constructible`.
Added holes: 2, each the complete body `:= by sorry` of a public theorem:

- `AlgebraicGeometry.ProEtale.FiniteModelQuotient.chart_comparison`
  (lem-sfb-finite-model-quotient-chart-comparison), only the derived chart comparison
  for a specified scalar resolution, with no cohomology or constructibility conclusion.
- `AlgebraicGeometry.ProEtale.FiniteModelQuotient.cohomology_descent`
  (lem-sfb-finite-model-quotient-cohomology-descent), descent of the supplied local
  calculation to individual cohomology sheaves, without coefficient finiteness,
  discreteness, boundedness or the chart calculation itself in the conclusion.

This is a decomposition, not a sorry-free proof of the mathematical result: 1 upper hole
closed, 2 lower holes added, net -1. All private helpers are proved. Definitions contain no holes.
The two-term kernel/cokernel arguments cover ranks zero and the zero map; the quotient-ring
argument uses positive exponent n+1. The descent proof plan treats an empty scheme and an empty
stratification explicitly, using one empty stratum for the positive-length intrinsic predicate.

## No longer needed

No mathematical dependency of the original seven-step plan is withdrawn: the coefficient,
K-flat, scalar-extension, pullback, cover-detection and open/closed tools remain needed
in the two new lower steps. The main proof needs them through those steps, rather than
through direct imports. The main node's proof_deps now describes the actual assembly.

Removed the unused direct CompletionTriangleComparison import: neither completion nor
its unit is used. Replaced the unused direct FiniteDiscreteOrdinaryEquivalence import by
FiniteDiscreteOrdinaryEncoding, whose encoding_exists theorem is sufficient. The finiteness
interface CoefficientExtensionFinite is now proof-only; the data module imports CoefficientExtension.
The following former private proof imports are no longer needed directly in the item;
most remain dependencies of the two proof plans, so this does not withdraw their nodes:

- `Sheaf.AlgebraicGeometry.IntegralConstantCompletion`
- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection`
- `Sheaf.SixFunctors.ConstructibleOpenClosedRefinement`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.FiniteDiscreteEncodingPullbackFixed`
- `Sheaf.Paper.FiniteDiscreteScalarConstantModels`
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`
- `Sheaf.CategoryTheory.ConstantFiniteFreePresentationExtension`
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`
- `Sheaf.Algebra.Homology.FiniteFreeResolutionTensor`
- `Sheaf.CategoryTheory.ScalarInverseImageTowerDiagram`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.ProEtaleFiniteModelStalks`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
- `Sheaf.Paper.CartesianCoefficients`
- `Mathlib.LinearAlgebra.FreeModule.PID`
- `Mathlib.LinearAlgebra.Dimension.Free`
- `Mathlib.CategoryTheory.Sites.LocalProperties`
- `Mathlib.Topology.Algebra.Valued.LocallyCompact`

No entire Lean module is withdrawn or asserted unreachable.

## Where the brief, the DAG or earlier work was wrong

The current blueprint moved the ctf-equals-bc proof to
sec-proetale-coefficients/sk-prop-integral-criterion/lem-integral-ctf-equals-bc.proof.md.
The nodes and docstrings in the existing item refer to an older location. New source records
use literature/blueprint/latest and keep the Local models, Locality and Strata route.
The original proof plan's prescribed mathematical dependencies are retained in the lower steps.
The existing statement and targets are unchanged.

## New nodes

`def-sfb-finite-model-quotient-coordinates` owns the unchanged coordinate declarations in the
new data module. This is extraction of existing definitions, not a new coefficient convention.

`lem-sfb-finite-model-quotient-chart-comparison` isolates restriction versus derived quotient
extension and the specified matrix representative, steps 2--4 of the original plan.

`lem-sfb-finite-model-quotient-cohomology-descent` isolates cover and finite-stratum descent
of cohomology and the two constructibility predicates, steps 6--7. Its assumed chart calculation
is explicitly produced by the parent proof from the first new lemma and proved algebra.

Each theorem has a source and complete proof in words in its docstring and node. Searches ran
through msearch (LeanSearch, Loogle/LeanFinder, grep); generic homology and tensor quotient
lemmas were found, but no existing theorem gives either specialized comparison or descent.
The unit sk-prop-sf-comp-coherence and its realized steps are unchanged.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
