## What changed

Partial proof delivery for `Sheaf.Paper.FiniteCounitRestrictionTowers`.
Six existing theorem holes are filled without changing their signatures or any definition.
`finitePoints` reuses the existing finite geometric-fibre instance. Direct-image additivity
follows from its right adjoint structure. Point-sum additivity follows by composing with the
product projections. `comparisonCounit` applies the existing iterated mate and counit identities.
The two strict transition squares are the naturality of `coefficientSequenceTransition` in
each complex degree. The actual identity germ is a colimit coprojection at the terminal object
of the opposite pointed-neighbourhood category, hence invertible.

The existing node's proof and proof origin record these arguments. Its Step 8 now uses the
proved initial-neighbourhood argument, removing two unnecessary dependencies. No new modules,
nodes, statements, definitions, or holes are introduced. All public imports are preserved.

## Proved and sorry left

All names below are in namespace `WeilConjectures.FiniteCounitTowers` and belong to node
`lem-zl-finite-counit-restriction-towers`.

Closed 6 of the original 14 named theorem holes:

- `finitePoints`.
- `push_additive`.
- `pointSum_additive`.
- `comparisonCounit`.
- `transitionSquares`.
- `etGerm_isIso`.

Added holes: 0. Split-off statements: 0. Remaining 8 existing named theorem holes:

- `pushExact` (node `lem-zl-finite-counit-restriction-towers`).
- `fixedDirect_eq` (node `lem-zl-finite-counit-restriction-towers`).
- `fixedPull_existsUnique` (node `lem-zl-finite-counit-restriction-towers`).
- `fixedExchange` (node `lem-zl-finite-counit-restriction-towers`).
- `fixedComponent` (node `lem-zl-finite-counit-restriction-towers`).
- `comparisonArrows` (node `lem-zl-finite-counit-restriction-towers`).
- `etComponent_stalk` (node `lem-zl-finite-counit-restriction-towers`).
- `finiteCounitRestrictionTowers` (node `lem-zl-finite-counit-restriction-towers`).

The remaining theorems retain their original statements and standalone `sorry` proofs.
This is a partial proof delivery, not a proof of the final tower theorem.

## No longer needed

Step 8 no longer uses nodes `lem-exc-etale-sheaves-gsets-point` or
`lem-weil-pbc-geometric-point-cohomology`: the actual germ is invertible by the universal
property of the initial identity neighbourhood. They are removed from Step 8's `uses`,
`proof_deps`, and top-level `tool_uses`. This does not withdraw either node or its module.
Other dependencies of the unfinished proof plan remain recorded.

Removed the following 22 private imports, unused by the completed proofs or already available
through the preserved public imports:

- `Sheaf.AlgebraicGeometry.FiniteFpProEtalePushforwardExact`.
- `WeilConjectures.SixFunctors.Finite.Exact`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`.
- `WeilConjectures.SixFunctors.Finite.BaseChange`.
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageMateCompatibility`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageComparisonCoherence`.
- `Sheaf.AlgebraicGeometry.Sites.EtaleSheavesGsetsPoint`.
- `Sheaf.AlgebraicGeometry.GeometricPointCohomology`.
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Paper.KFlatMapFactorization`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `Sheaf.Paper.PointProEtaleSectionsExactOfUniverses`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`.
- `Sheaf.CategoryTheory.DerivedExactMate`.

No Lean module is withdrawn. Removing a redundant import here does not assert that its
module is absent from the targets' wider import closure.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The DAG's germ argument was longer than necessary:
it passed through the Galois-set classification and geometric-point cohomology, whereas
the actual germ itself is an invertible colimit coprojection at the identity neighbourhood.
The strict quotient squares likewise follow immediately from the naturality of the already
constructed coefficient-transition transformation; no elementwise reconstruction is needed.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
