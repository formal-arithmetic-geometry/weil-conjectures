## What changed

Proved `WeilConjectures.sfFieldShriekCompositionRational_existsUnique` in
`Sheaf.Paper.FieldShriekCompositionQcqs`. The component is the localization of the
integral compositor. Naturality is proved by tensor induction from integral
naturality and the pure tensor formula for the fixed compact-support Hom maps;
component extensionality proves uniqueness. The helper
`rationalSupport_map_tmul` is proved and the tensor-product tower import is retained.

Pruned unused proof-only imports, retaining the required unit-route import. The
public imports remain unchanged, and the module compiles with the two direct holes
listed below.

## Proved and sorry left

Closed one original hole:

- `WeilConjectures.sfFieldShriekCompositionRational_existsUnique` (node
  `lem-zl-field-shriek-composition-qcqs`).

Two original holes remain:

- `WeilConjectures.sfFieldShriekCompositionIntegral_existsUnique` (node
  `lem-zl-field-shriek-composition-qcqs`).
- `WeilConjectures.sfFieldShriekCompositionQbar_existsUnique` (node
  `lem-zl-field-shriek-composition-qcqs`).

No holes were added and no statements or definitions were changed.

## No longer needed

The following proof-only imports were removed because no surviving declaration in
this module references them: `WeilConjectures.Compactification.NagataCompactification`,
`Sheaf.AlgebraicGeometry.CompatibleCompactificationTriangle`,
`Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`,
`Sheaf.Paper.ProEtaleConstructibleOrigin`, `Sheaf.Paper.IntegralResidueTor`,
`Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`,
`Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`,
`Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`, `Sheaf.Paper.FiniteTorAmplitude`,
`Sheaf.Paper.SfIntegralConstructible`,
`Sheaf.Paper.SfDerivedComplete`,
`Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`,
`WeilConjectures.Compactification.CategoryBaseChange`,
`Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`,
`Sheaf.Paper.PbcRationalTransport`, `Sheaf.Paper.SfScalarExtensionComposition`,
`Sheaf.CategoryTheory.StageSystemFunctorDescent`,
`Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars`,
`Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage`,
`Sheaf.AlgebraicGeometry.CompactificationRefinementCoherence`,
`Sheaf.Paper.BasicOperationsCoefficientReduction`,
`Sheaf.Paper.SfIntegralCompactSupportConstructible`,
`Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`, and
`Sheaf.SixFunctors.IntegralCompactificationSystemRealization`.

The unit-route import `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility` is retained. No DAG nodes or modules were withdrawn. The retained route is the existing node's raw rationalization step. Its step 6 is updated to record the actual tensor-induction proof; `prop-weil-pbc-rational-transport` is removed from that step, the proof dependencies, and the obsolete tool-use entry because its transport theorem is not used. Dependencies of the two unfinished arguments remain in the node. Validation: the sandbox `lcompile.py --all` passes in 10.0 seconds. The earlier dry run passed before restoration of the unit-route import; the final packet is checked again below.

## Where the brief, the DAG or earlier work was wrong

The earlier interrupted attempt reported a missing published
`RefinementCategory.olean`; the current sandbox compiles after import pruning, so
that was a transient build or server artifact issue. The integral and algebraically
closed coefficient steps still require the substantial system-realization and
coefficient-compatibility arguments described by the node; they were not replaced
by weaker statements.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
