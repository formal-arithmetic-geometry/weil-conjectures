## What changed

Replaced the sorry in
`WeilConjectures.FrameworkPbc.frameworkPbcPullbackScalarBridge` by a complete Lean
assembly. The existing simultaneous realization theorem supplies the common
realization and its coefficient coherence. Two new steps supply integral comparison
laws and raw localization of those fixed laws. The assembly explicitly fills every
System field and both RawCoherence fields, retaining the original signatures.
Updated the parent node's proof, proof dependencies and proof origin to match.
No definition, target statement, public import, or existing declaration signature changed.

## Proved and sorry left

Decomposition, not a complete proof from sorry-free dependencies: closed the one
original hole in
`WeilConjectures.FrameworkPbc.frameworkPbcPullbackScalarBridge` and added two holes:

- `WeilConjectures.FrameworkPbc.frameworkPbcIntegralComparisonLaws`
  (`lem-pur-framework-pbc-integral-comparison-laws`).
- `WeilConjectures.FrameworkPbc.frameworkPbcRawComparisonLaws`
  (`lem-pur-framework-pbc-raw-comparison-laws`).

The item module has zero remaining sorry. Each new theorem has exactly one whole-body
sorry, its own module, source, complete proof plan and DAG node. The integral step
concludes only integral families and laws for a prescribed realization. The raw step
assumes fixed integral families and four laws and concludes only their restrictions
and rationalizations. Neither is the original existential System theorem under a new
name. Net hole change in this packet is +1. The existing simultaneous-realization
hole is imported unchanged.

Validation: compiling all three modules together through lcompile.py passed. The
first isolated assembly compile saw an older raw-comparison artifact (an obsolete
realization_coherent argument); the all-source compile uses the current source and
passes. Edge cases checked in the split: identity scheme morphisms, empty schemes,
identity coefficient extension, coefficient towers, arbitrary morphisms and ramified
quotient maps. No quotient-ring flatness or exchange invertibility is introduced.

## No longer needed

Removed the following proof-only imports from the item module:

- `Sheaf.Paper.CompletedCoefficientPresentationTransport`.
- `Sheaf.Paper.AdicPullbackPresentationTransport`.
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.CategoryTheory.StrictRoosComparison`.
- `Sheaf.Paper.IntegralOperationsWellDefined`.
- `Sheaf.Paper.CompletedOperationTowerSubstitution`.
- `Sheaf.Paper.CompletedIntegralFiniteFree`.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`.
- `Sheaf.Paper.IntegralAmbientOperationModels`.
- `Sheaf.Paper.PbcQbarCompletedPullback`.
- `Sheaf.CategoryTheory.FiniteFreeCompletionTransport`.
- `Sheaf.Paper.WeilCompletedTensorReflector`.
- `Sheaf.Paper.ConstantCompletionEquivalence`.
- `Sheaf.CategoryTheory.ReflectedAdjunctionCoefficientSquares`.
- `Sheaf.SecSmoothPurity.StrictCoefficientComparisonCalculus`.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`.
- `Sheaf.Paper.SfRationalizationKaroubi`.
- `Sheaf.Paper.PbcRationalCategory`.
- `Sheaf.Paper.CompletedPullbackReflection`.

These mathematical steps remain in the integral or raw split's proof plan and remain
needed transitively. This is import cleanup, not withdrawal of their modules or
proof obligations. No module or node is claimed pruned. The simultaneous realization
import stays; the two new imports supply the genuine remaining steps. No blueprint
unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The draft sandbox was already present when this worker turn began; it contained the
two split statements and assembly but no report. I reviewed their statements against
the original System and RawCoherence fields and completed the delivery records.
The older blueprint path in the original node is historical. New nodes and proof
origins cite the current latest coefficient-change proof, paragraphs (2)--(3), and
explicitly identify the strict-tower argument as the agent-written refinement of the
parent proof. No mathematical statement correction is proposed. Existing lower-level
declarations do not directly assemble all normalized integral and raw fields; the
remaining work is recorded honestly in the two split obligations.

## New nodes

`lem-pur-framework-pbc-integral-comparison-laws`, module
`Sheaf.Paper.FrameworkPbcIntegralComparisonLaws`: the integral construction and
coherence argument (parent Steps 1--7) for a prescribed coherent realization, without
raw rationalization. Its proof keeps the original whole-tower, finite-free scalar,
tensor and signed-shift argument and dependencies.

`lem-pur-framework-pbc-raw-comparison-laws`, module
`Sheaf.Paper.FrameworkPbcRawComparisonLaws`: restriction and raw scalar localization
of fixed integral comparison data (parent Step 8), without constructing the integral
families. It includes separately localized unit and composition maps and both raw
scalar/tensor squares. Both nodes use the current blueprint source and the recorded
Loogle, Lean Finder, LeanSearch and repository searches. No change record is needed:
all old signatures and definitions are unchanged, and all new interfaces live in
new modules.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
