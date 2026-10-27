# constructibleComparisonPullback_exact_faithful

## Reason

The item needs the existing intrinsic exactness theorem to form its derived adjunction.
Its module publicly imported the final constructible-comparison theorem, which itself
imports this item. The exactness proof only uses the canonical constructions in the
comparison-data module. Narrowing that import removes the cycle and preserves every
existing declaration, signature, attribute and proof body in the exactness module.
No source-library module changes. No target statement or definition changes. The exactness node’s stale statement/proof
dependency on the final theorem is repointed to `lem-pe-coefficient-comparison-data`,
which now owns the identical canonical constructions; the mathematical statement is unchanged.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
```

## New

```lean
public import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonData
```

The declaration is identical before and after:

```lean
theorem constructibleComparisonPullback_exact_faithful (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    PreservesFiniteLimits (constructibleComparisonPullback X A) ∧
      (constructibleComparisonPullback X A).Faithful
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ConstructibleComparisonModuleExact
--uses constructibleComparisonPullback_exact_faithful` lists the exactness module
and the two existing consumers below. The module has two direct Lean importers.
Both are checked unchanged against the narrowed import. The large transitive closure
has no changed declarations: the only possible visibility effect is at these direct
importers. The tensor-test module publicly imports the final comparison itself; the
finite-model module explicitly imports the comparison data and its other requirements.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConstructibleComparisonModuleExact | unclaimed | Narrow its first public import; all declarations and proof bodies unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleComparisonTensorTestReflection | unclaimed at inspection | Unchanged consumer; has its own public final-comparison import. |
| Sheaf.Paper.FiniteComparisonModelRealization | unclaimed at inspection | Unchanged consumer; has its own data import and explicit proof imports. |
| Sheaf.AlgebraicGeometry.CoefficientBoundedClassicalDescent | D7 | Adds a private proof import of exactness and uses its finite-limit clause. |

## Status

landed 20261025T201637-L-2594403 2026-10-25 (merge of deliver/D7/Sheaf.AlgebraicGeometry.CoefficientBoundedClassicalDescent)
