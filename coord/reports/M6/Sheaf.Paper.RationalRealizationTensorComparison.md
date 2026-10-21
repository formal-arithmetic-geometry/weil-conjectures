## What changed

In `Sheaf.Paper.RationalRealizationTensorComparison`, proved
`WeilConjectures.constructibleTensorCompletionPresentation` from
`WeilConjectures.constructibleTensorCompletion`: eliminate the three existential
witnesses, extract the descended comparison, and put the four witnesses and four
normalization clauses into the existing record. No data or equation is weakened.
The main comparison theorem and every declaration signature remain unchanged.

Made the definitional conversion for the finite total-tensor section explicit in
`ConstructibleTensorCompletionNormalized`, and used local transparency controls to
avoid unfolding the tensor and typed functors during elaboration. The full candidate
compiled without errors or warnings in 55.7 seconds. See the change record
`coord/changes/M6-tensor-completion-normalization-elaboration.md`.

The node's step 2 records the implemented presentation helper; its remaining route
and all dependencies are retained because the main comparison proof is unfinished.

## Proved and sorry left

Closed one of the two original holes:
`WeilConjectures.constructibleTensorCompletionPresentation`.
This is a complete Lean proof from the existing tensor-completion declaration;
that dependency is itself still admitted in its own module.

One original hole remains unchanged:
`WeilConjectures.RationalTensorRealization.rational_realization_tensor_comparison`
(node `lem-zl-rational-realization-tensor-comparison`). Its docstring retains the
complete seven-step argument. The ordinary scalar-extension comparison, transport
of its normalized tensor constraints through completion and localization, and
finite-field compatibility have not been constructed in Lean in this delivery.

Added zero holes and split off zero statements. No new definitions contain `sorry`.

## No longer needed

Removed the following private proof imports, unused by the implemented proof and
by the existing interfaces:

- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `Sheaf.Paper.CompletedOperationTowerSubstitution`
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
- `Sheaf.Paper.ScalarExtensionTowerCoherence`
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.SfRationalizationKaroubi`
- `Sheaf.Paper.DerivedPullbackTensorHom`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`

These removals prune imports only. No mathematical dependency of the unfinished main
theorem is claimed unnecessary; its planned nodes and modules remain in the DAG.
No public import, declaration, node, unit route, or source-library module is removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The presentation helper is exactly the
repackaging claimed in its docstring. The main seven-step plan remains unimplemented;
this delivery closes the separate presentation hole only. Implicit conversion of
the finite tensor section caused expensive unfolding; the definitionally equal
explicit conversion and local settings make the completed helper compile in the
whole module within the existing limit. No compile limit or launcher script changed.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
