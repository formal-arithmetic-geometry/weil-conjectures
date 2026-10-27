## What changed

Filled the whole-system localization equation, finite-level generator formula,
both strict Roos coordinates, completion augmentation coordinates, and naturality
calculation in `Sheaf.Paper.ExplicitScalarConeWordCoordinates`. Every existing
public declaration and definition keeps its signature.
No other existing Lean module is edited.

The finite-level proof conjugates the strict-cone comparison by the canonical
isomorphism between the ordinary scalar models. Its normalization at tensor-unit
generators identifies it with `scalarPullbackLevel` by uniqueness. Naturality of
the reduction tensor section and of the finite pullback adjunction unit then
transports the full generator formula. The three supporting helpers are private
and proved, and introduce no new proof obligations.

The new proof-only imports are `Sheaf.Paper.IsomorphismComparisonScalarExtension`,
`Sheaf.Paper.IntegralReductionTowerUnrestricted` (including its private proved
reduction equations), and `Sheaf.Paper.ScalarRoosComparison` (including its private
proved tower-coordinate equation). These private implementation lemmas avoid
restating existing reduction and Roos calculations.

The system equation uses the defining normalization of
`integralComparisonSystemScalarPullback`. The two cone coordinates follow by
precomposing the existing strict Roos tower-coordinate equations with the recorded
scalar Roos map. The augmentation is the defining property of
`integralScalarCompletionChain`. Naturality is the composition of the naturality
squares for the primitive realization maps, the actual intermediate counit,
and the entire-system scalar/pullback comparison.

## Proved and sorry left

Validated by `lcompile.py`: compiled successfully in 47.5 seconds.
Original holes: six; holes closed: five; holes added: zero; holes remaining: one.

The five holes closed, all in namespace `WeilConjectures.ExplicitScalarCone`, are:

- `explicitScalarConeSystemCoordinates`
- `explicitScalarConeLevelCoordinates`
- `explicitScalarConeBothCoordinates`
- `explicitScalarConeAugmentationCoordinates`
- `explicitScalarConeWordCoordinates_naturality`

The sole remaining original hole is
`WeilConjectures.ExplicitScalarCone.explicitScalarConeWordCoordinates`, with node
`lem-pod-explicit-scalar-cone-word-coordinates`. Its statement and original ten-step
sourced proof docstring are unchanged. No holes are split off, and no other
module gains a hole. The supplementary declarations share the same item node;
its proof now records their direct arguments while retaining the main proof plan.

## No longer needed

Removed the direct proof imports below. The retained public imports provide the
statements and their underlying constructions. These removals do not withdraw
any node or module: the original dependency plan for the remaining main theorem
is retained.

- `Sheaf.Paper.IsomorphismScalarTensorKFlatModel`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent`
- `Sheaf.Paper.CoefficientExtensionReductionModel`
- `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization`
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
- `Sheaf.Paper.CompletionUnitStrictQuotientModel`
- `Sheaf.CategoryTheory.StrictRoosComparison`
- `Sheaf.Paper.IsomorphismComparisonNatural`
- `Sheaf.Paper.SequenceScalarGeneratorInterchange`
- `Sheaf.Paper.IsomorphismScalarAugmentationCone`

## Where the brief, the DAG or earlier work was wrong

The strictly defined localization, cone-coordinate and augmentation clauses have
shorter proofs than the general representative argument in the node. The complete
word equality still needs that normalization argument; none of those hypotheses
has been removed or replaced by finite-evaluation faithfulness.

The strict-cone data use `completedOrdinaryScalarExtension`, whereas the item uses
`integralOrdinaryScalar`. They must be related by their canonical generator-normalized
isomorphism before applying the strict-data generator formula.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
