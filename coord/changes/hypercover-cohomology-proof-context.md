# AlgebraicGeometry.hypercover_cohomology proof context

## Reason

The stage-3 static checker conservatively classifies added `universe`, `open`, `variable`,
and section commands as an interface change. This record documents the proof context.
Every helper declaration is private. The existing theorem's signature and visibility,
and both existing public imports, are identical. New imports are proof-only.
No definition used by a target has changed and no target statement requires a new review.

The coefficient functor's preservation of finite colimits is proved as the private theorem
`HypercoverCohomologyProof.coeffFiniteColimits`. It is installed only through local bindings inside
the comparison proof and the final theorem proof. No new global instance is registered.

## Old

The original context used `universe u₁`, `open CategoryTheory`, and namespace
`AlgebraicGeometry`. The theorem signature was:

```lean
theorem hypercover_cohomology (X : Scheme.{u₁}) [CompactSpace X] [QuasiSeparatedSpace X]
    (q : ℕ) :
    FiniteSplitEtaleHypercover.IsCohomologyColimit AddCommGrpCat.{u₁ + 1} q
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u₁ + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u₁ + 1} X (q : ℤ)) ∧
    ∀ (R : Type (u₁ + 1)) [Ring R],
      FiniteSplitEtaleHypercover.IsCohomologyColimit (ModuleCat.{u₁ + 1} R) q
        (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u₁ + 1} R)) 0 ⋙
          Etale.cohomology (ModuleCat.{u₁ + 1} R) X (q : ℤ))
```

## New

The theorem signature remains exactly:

```lean
theorem hypercover_cohomology (X : Scheme.{u₁}) [CompactSpace X] [QuasiSeparatedSpace X]
    (q : ℕ) :
    FiniteSplitEtaleHypercover.IsCohomologyColimit AddCommGrpCat.{u₁ + 1} q
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u₁ + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u₁ + 1} X (q : ℤ)) ∧
    ∀ (R : Type (u₁ + 1)) [Ring R],
      FiniteSplitEtaleHypercover.IsCohomologyColimit (ModuleCat.{u₁ + 1} R) q
        (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u₁ + 1} R)) 0 ⋙
          Etale.cohomology (ModuleCat.{u₁ + 1} R) X (q : ℤ))
```

Added private helper scope `AlgebraicGeometry.HypercoverCohomologyProof` contains sections
`Homotopy`, `Transport`, `Cochains`, and `Derived`, with explicitly bound universe and
category variables. Additional opens are `CategoryTheory.Limits`, `CategoryTheory.Functor`,
`Opposite`, `AlgebraicTopology`, `AlgebraicGeometry.FiniteSplitEtaleHypercover`, and the
`Simplicial` notation scope. These are local elaboration context, not exported declarations.
All comparison definitions are actual constructions, and all helper theorems are proved.

## Users

`tools/downstream.py WeilConjectures.AlgebraicGeometry.HypercoverCohomology --uses
AlgebraicGeometry.hypercover_cohomology` lists five downstream modules and three textual
uses including the item itself. All are covered below. No downstream adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.AlgebraicGeometry.HypercoverCohomology | E2 | Original theorem proved; signature and public imports identical; private proof helpers added. |
| Sheaf.AlgebraicGeometry.ComparisonDirectImage | unclaimed | Unchanged theorem interface and public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedCohomologyContinuity | unclaimed | Unchanged theorem interface and public import closure; no adaptation. |
| Sheaf.Paper.HypercoverCohomology | unclaimed | Its duplicate wrapper and imports are unchanged; no adaptation. |
| Sheaf.Paper.HypercoverCohomologyAbelian | unclaimed | The projection uses the same theorem signature; no adaptation. |
| WeilConjectures | unclaimed | Reexports the same source interface; no adaptation. |

## Status

landed 20261015T230601-L-3095301 2026-10-15 (merge of deliver/E2/WeilConjectures.AlgebraicGeometry.HypercoverCohomology)
