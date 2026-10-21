# WeilConjectures.scalarCompletionAssociator proof context

## Reason

The proof uses existing normalized scalar declarations of
`Sheaf.Paper.CompletedLineTensorCoherence`, a private proved generic restriction helper,
and local irreducibility to avoid unfolding the published completed scalar constructions.
No public signature, data definition, instance or public import changes. No consumer
needs adaptation. The assigned module has no current Lean importers; its DAG parents
remain present, and the module and its entire interface are preserved.

## Old

```lean
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite
```

The proof-only imports were `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`,
`Sheaf.Paper.ConstantCompletionEquivalence`,
`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.Algebra.Homology.ChangeOfRingsKFlat`, and
`Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`.

## New

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
```

The proof-only import is `Sheaf.Paper.CompletedLineTensorCoherence`.
The following attributes are local to this module:

```lean
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted completedCoefficientMap
  completedOrdinaryScalarExtension completedDerivedScalarExtension
  completedScalarCounit completedScalarTensorSection integralScalarExtensionOfUniverses
  completedScalarChangeData completedScalarChainComparison
  completedScalarComparison completedScalarIdentityMultiplication completedScalarIdentityUnit
```

`comparisonAlong` is private and fully proved. All public definitions retain their
original bodies, and the structure and theorem retain their original statements.
No target review reopens. The assembled associator exposes its published objectwise
components directly through `NatIso.ofComponents`; naturality comes from the
composed comparisons. Profiling the initial presentation identified repeated unfolding
of those comparisons. The final whole file compiles cleanly in 53.6 seconds with the
unchanged 60-second limit.

## Users

`python3 tools/downstream.py Sheaf.Paper.ScalarCompletionAssociator
--uses scalarCompletionAssociator` reports zero downstream modules and the declaration
occurrence in the item itself. No module is withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ScalarCompletionAssociator | B6 | Complete the existing proof; preserve its interface. |

## Status

landed 20261021T125952-L-2472867 2026-10-21 (merge of deliver/B6/Sheaf.Paper.ScalarCompletionAssociator)
