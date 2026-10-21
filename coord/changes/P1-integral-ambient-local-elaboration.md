# IntegralAmbient local proof elaboration

## Reason

The completed-coefficient and tensor constructions contain large chosen localization and
sheafification terms. The new proofs need the cone projection API without unfolding those
terms. Local reducibility attributes keep the tensor object and augmentation opaque while
checking the coordinate comparisons; explicit unfolding is used in their proved helpers.
The final statement is elaborated with its derived functors opaque. These are local commands,
not definition or statement repairs. The preflight classifies changes to commands such as
`open` and `attribute` as requiring this record.

The file compiles in 29.3 seconds through lcompile.py. The original signatures, public
imports, instance attributes and non-theorem bodies are unchanged. No source-library module
is modified. No target meaning or consumer interface changes.

## Old

```lean
attribute [local irreducible] coefficientMap push pull pullTowerIso tensorTowerIso
  IntegralOnSlice.duality IntegralOnSlice.completion IntegralOnSlice.completionComparison
  IntegralOnSlice.completionUnit HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted unrestrictedIntegralReductionExistence
```

There was no local tensor reducibility restoration or final derived-functor attribute block,
no `open AlgebraicGeometry.Scheme` inside the namespace, and no `set_option linter.all false`.

## New

```lean
set_option linter.all false
```

The namespace additionally opens `AlgebraicGeometry.Scheme`. The cone helper has a scoped
`open CochainComplex CochainComplex.HomComplex in`, applying only to that private theorem.

```lean
attribute [local irreducible] coefficientTotalTensor
  coefficientMap push pull pullTowerIso tensorTowerIso
  IntegralOnSlice.duality IntegralOnSlice.completion IntegralOnSlice.completionComparison
  IntegralOnSlice.completionUnit IntegralOnSlice.roosUnit HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted unrestrictedIntegralReductionExistence
```

Before the original total-tensor goodness theorem:

```lean
attribute [local semireducible] coefficientTotalTensor
```

Before the final original statement:

```lean
attribute [local irreducible] integralDerivedPullback integralCompletedTensor
  integralDerivedPullbackComparison integralCompletedTensorComparison
  integralOperationsPullbackTowerFunctor integralOperationsTensorTowerFunctor
  integralOperationsGoodComplex tensorRepresentative
```

The local attributes control proof elaboration within the existing section. They do not
change the definitions' values. The linter option suppresses redundant module lint work;
kernel checking and all delivery checks still run.

## Users

`python3 tools/downstream.py Sheaf.Paper.IntegralAmbientOperationModels` reports zero current
Lean downstream modules. The declaration-use query for `tensorOperationUnit_coordinates`
reports only this item. DAG parents and the unfinished original statements are retained;
zero current importers is not used to withdraw any declaration or module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralAmbientOperationModels | P1 | Local proof elaboration only; six theorem proofs filled; original signatures and definitions preserved. |

No consumer adaptation is necessary. Future importers retain the same public declarations
and public imports.

## Status

landed 20261021T134519-L-1278540 2026-10-21 (merge of deliver/P1/Sheaf.Paper.IntegralAmbientOperationModels)
