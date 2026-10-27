## What changed

The item proves `comparisons_existsUnique` from the existing normalized scalar total-tensor
and pullback total-tensor comparisons, and proves `derivedSigma_existsUnique` by resolving
representatives and tensor-comparison descent. The existing `unit` proof is adapted.
No source-library module is edited. No new mathematical lemma is split off.

The definition repair records the same categorical composites through generic helpers,
replaces the four-field concrete record by a specialization of `ComparisonData`, and gives
the signed total tensor an explicit functor type. The five-map Roos equation uses HEq at
the same fixed endpoints; `fiveStepEquation_iff_eq` proves equivalence to the original
ordinary equality. `DerivedSigmaModel` is locally irreducible after its definition.
These repairs address repeated elaboration and type checking of large concrete terms.
The change record is `coord/changes/x7-scalar-tower-categorical-cache.md`.
The final item compiled in 54.3 seconds. An ordered scratch check compiled the changed
item and both unchanged consumers, `CompletedComparisonQuotientRealizationDefs` and
`CompletedComparisonQuotientRealization`. No consumer adaptation is needed.
The local proof context also keeps the chosen left adjoint and derived functor folded,
and uses the defining dependency's backward-definitional-equality setting.

## Proved and sorry left

Closed two of the seven original holes:
`WeilConjectures.ScalarExtensionTower.comparisons_existsUnique` and
`WeilConjectures.ScalarExtensionTower.derivedSigma_existsUnique`.
The original `unit` theorem remains proved. No holes are added.

Five original holes remain, all attached to `lem-pur-scalar-extension-tower-coherence`:
`WeilConjectures.ScalarExtensionTower.square`,
`WeilConjectures.ScalarExtensionTower.composition`,
`WeilConjectures.ScalarExtensionTower.realizationModels`,
`WeilConjectures.ScalarExtensionTower.scalarExtensionTowerCoherence`, and
`WeilConjectures.ScalarExtensionTower.quotientModels`.

## No longer needed

Removed unused private imports of `Sheaf.Algebra.Homology.KFlatTotalTensorModel`,
`Sheaf.Paper.KFlatRingedToposPullback`,
`Sheaf.Paper.IntegralDerivedOperationsOnSlices`, and
`Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
Their public declarations needed by the statements remain available through the
original public imports. No module withdrawal or whole-node pruning is claimed.
The strict square, quotient association, and completed realization arguments remain
in the DAG because their original holes remain. The completed comparison dependencies
are preserved, including the quarantined normalized realization node.

## Where the brief, the DAG or earlier work was wrong

`Sheaf.Paper.NormalizedScalarComparisonRealization` is absent from the current Lean
tree and was recovered only for inspection in scratchpad. Its existentially supplied
models do not directly prove equations for the arbitrary normalized models required
by this item. No archive is deleted or withdrawn. The DAG now records the actual
proofs of comparison uniqueness and derived comparison descent, while retaining the
unfinished original route. Generic categorical interfaces are a compilation repair;
no Challenge target signature, quotient map, transition, or normalization requirement
is weakened.

The existing `primitiveQuotientRealizationComparisons` dependency is itself marked
STATEMENT-DISPUTED: its finite presentation conditions may not determine the derived
morphism required by its normalization. This delivery does not use that disputed
existence theorem, change the realization statements, or remove their dependency route.

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
