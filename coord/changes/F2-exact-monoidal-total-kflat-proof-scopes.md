# CategoryTheory.Equivalence.exactMonoidal_totalTensor_kFlat

## Reason

The stage-3 static preflight requires a change record for the added scope commands
around private proof helpers. The mathematical statement, every existing public import,
and every public declaration signature remain verbatim. No public definition is added
or changed. This record documents the scope/attribute commands rather than a statement
or definition repair.

`open ZeroObject` enables zero-object notation within this file. Each `omit ... in`
removes unused section typeclasses from a single private helper. Each
`set_option backward.isDefEq.respectTransparency false in` affects elaboration of just
the following private proof. `@[reassoc]` supplies a reassociated private summand lemma;
`@[instance_reducible]` marks the two private monoidal-structure constructions for local
instance elaboration. None is a global instance or an exported notation declaration.
The constructed structures contain no postponed proof or data.

## Old

The existing open command, verbatim:

```lean
open CategoryTheory CategoryTheory.Limits MonoidalCategory
```

There were no private proof helpers, helper attributes, `omit` commands or local
transparency options at this position. The theorem body was exactly:

```lean
:= by
  sorry
```

## New

The open commands, verbatim:

```lean
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open ZeroObject
```

The local commands are attached only to the newly added private helpers:

```lean
omit [SymmetricCategory M] [SymmetricCategory A] in
set_option backward.isDefEq.respectTransparency false in
```

The longer omission lists only remove unused section hypotheses from the private
acyclicity and flatness helpers. The attributes are exactly `@[reassoc]` on
`tensorComparison_ι` and `@[instance_reducible]` on `complexOplax` and `complexMonoidal`.
The new complete theorem proof and all helper bodies are in the delivered Lean module.
The old and new public theorem signatures are identical, including all binders,
universes, hypotheses, and the entire conjunction of conclusions.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.ExactMonoidalEquivalenceTotalKFlat
--uses exactMonoidal_totalTensor_kFlat` lists these consumers. Only
`Sheaf.CategoryTheory.ConstantScalarRestrictionTensor` directly imports this module
and calls the theorem (line 492); its destructuring of the same conclusion remains
valid. No consumer needs a change, because there is no public interface change.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Algebra.Homology.ExactMonoidalEquivalenceTotalKFlat` | F2 | Proof filled; public signature unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteDiscreteCtfOrigin` | unclaimed | Transitive consumer; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.FiniteDiscreteCtfRealization` | unclaimed | Transitive consumer; no adaptation needed. |
| `Sheaf.CategoryTheory.ConstantModuleDerivedComparisonData` | unclaimed | Transitive consumer; no adaptation needed. |
| `Sheaf.CategoryTheory.ConstantModuleDerivedProjectionIdentification` | unclaimed | Transitive consumer; no adaptation needed. |
| `Sheaf.CategoryTheory.ConstantModuleGeometricComparisonData` | unclaimed | Transitive consumer; no adaptation needed. |
| `Sheaf.CategoryTheory.ConstantModulePlusComparisonData` | unclaimed | Transitive consumer; no adaptation needed. |
| `Sheaf.CategoryTheory.ConstantScalarRestrictionTensor` | U9 | Direct theorem consumer; no adaptation needed. |
| `Sheaf.CategoryTheory.DerivedProjectionComparisonSquares` | unclaimed | Transitive consumer; no adaptation needed. |
| `Sheaf.Paper.BrownHypothesesGeneration` | unclaimed | Transitive consumer; no adaptation needed. |
| `Sheaf.Paper.FiniteComparisonLocalizing` | unclaimed | Transitive consumer; no adaptation needed. |
| `Sheaf.Paper.FiniteComparisonPresentation` | unclaimed | Transitive consumer; no adaptation needed. |
| `Sheaf.Paper.IntegralAmbientCoefficientPresentation` | unclaimed | Transitive consumer; no adaptation needed. |
| `Sheaf.Paper.IntegralAmbientDirectImageEncoding` | unclaimed | Transitive consumer; no adaptation needed. |
| `Sheaf.Paper.IntegralAmbientTowerComparison` | unclaimed | Transitive consumer; no adaptation needed. |
| `Sheaf.Paper.IntegralCoefficientModelRealization` | unclaimed | Transitive consumer; no adaptation needed. |
| `Sheaf.Paper.OpenScalarFlatModelRealization` | unclaimed | Transitive consumer; no adaptation needed. |
| `Sheaf.Paper.OpenScalarSiteCoherence` | unclaimed | Transitive consumer; no adaptation needed. |
| `Sheaf.Paper.SystemRefinementConstructibleDomain` | unclaimed | Transitive consumer; no adaptation needed. |
| `Sheaf.SixFunctors.FiniteCompactProetale` | unclaimed | Transitive consumer; no adaptation needed. |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | unclaimed | Transitive consumer; no adaptation needed. |
| `Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness` | unclaimed | Transitive consumer; no adaptation needed. |

## Status

landed 20261023T123510-L-1199406 2026-10-23 (merge of deliver/F2/Sheaf.Algebra.Homology.ExactMonoidalEquivalenceTotalKFlat)
