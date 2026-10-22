# AlgebraicGeometry.Scheme.OrderedExchange.LambdaNormalization

## Reason

Retain the universal right-derived-limit comparison equation before conjugating by
the two exact-restriction factorization isomorphisms. This matches the output of the
existing `towerComparison_existsLimitIso` API. The former definition immediately
cancelled those isomorphisms; rebuilding that cancellation at the concrete site made
the kernel check of `lambda_existsUnique` take about 23 seconds. The equivalent equation
reduces that check to about 4 seconds. The whole module then compiles in 29.3 seconds.

For each complex, put `a` equal to the inverse restriction factorization at its ordinary
limit and put `b` equal to derived limit applied to the tower restriction factorization.
The new equation is `a.hom ≫ u ≫ e = v ≫ w ≫ b.inv`; the old equation is
`u ≫ e ≫ b.hom = a.inv ≫ v ≫ w`. These are equivalent by postcomposition with
`b.hom` and cancellation of `a.hom`, or by the inverse operations. The other four maps
are exactly the same source unit, comparison, ordinary limit comparison and target unit.
This holds for every complex, without a K-injectivity hypothesis. The existence theorem
retains this equation on every complex; K-injectivity is used only to prove uniqueness.

A diagnostic copied the old definition verbatim and proved both implications at every
complex by this generic isomorphism-cancellation argument. It compiled in 25.4 seconds.
No declaration signature changes and no comparison unit is replaced.

## Old

```lean
def LambdaNormalization (T : Scheme.{t})
    (e : completedRlim T (d.completedRing T) ⋙ res d T ≅
        exchangeTowerRes d T ⋙ rlim (A := A) T) : Prop :=
  ∀ P : CochainComplex (d.towers T) ℤ,
        (res d T).map (limitComplexUnit T (d.completedRing T) P) ≫
            e.hom.app (DerivedCategory.Q.obj P) ≫
            (rlim (A := A) T).map
              ((exchangeTowerModuleRes d T).mapDerivedCategoryFactors.hom.app P) =
          (reductionRestrict T (exchangeScalar d T)).mapDerivedCategoryFactors.hom.app
              (((completedTowerLimit T (d.completedRing T)).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (ordinaryLambda d T) (.up ℤ)).hom.app P) ≫
            limitComplexUnit T (exchangeConstantRing T A)
              (((exchangeTowerModuleRes d T).mapHomologicalComplex (.up ℤ)).obj P)
```

## New

```lean
def LambdaNormalization (T : Scheme.{t})
    (e : completedRlim T (d.completedRing T) ⋙ res d T ≅
        exchangeTowerRes d T ⋙ rlim (A := A) T) : Prop :=
  ∀ P : CochainComplex (d.towers T) ℤ,
    (reductionRestrict T (exchangeScalar d T)).mapDerivedCategoryFactors.inv.app
          (((completedTowerLimit T (d.completedRing T)).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (res d T).map (limitComplexUnit T (d.completedRing T) P) ≫
          e.hom.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinaryLambda d T) (.up ℤ)).hom.app P) ≫
        limitComplexUnit T (exchangeConstantRing T A)
          (((exchangeTowerModuleRes d T).mapHomologicalComplex (.up ℤ)).obj P) ≫
            (rlim (A := A) T).map
              ((exchangeTowerModuleRes d T).mapDerivedCategoryFactors.inv.app P)
```

## Users

`tools/downstream.py Sheaf.Paper.OrderedExchangeCoefficientComparison --uses LambdaNormalization`
lists 46 downstream modules and one declaration-user module:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | T3 | Prove the two derived comparisons using equivalent presentations of the specified normalizations. |

The three direct importers are `Sheaf.Paper.CompletedExchangeCoherence`,
`Sheaf.Paper.PulledReductionComparisonData`, and
`Sheaf.Paper.PulledReductionStrictTowerComparison`. None explicitly uses this predicate.
No other module needs adaptation. Their unchanged sources are checked against the changed
item. No declaration signature or target statement changes. The definition change reopens
review of any target whose meaning uses it; the independent reader should confirm that
the normalization equivalence preserves that meaning.

The normalization equivalence check passed. The final item compiled in 31.9 seconds.
All three unchanged direct importers compiled against it, in 5.3, 7.2 and 26.2 seconds
respectively.

## Status

landed 20261022T020117-L-34354 2026-10-22 (merge of deliver/T3/Sheaf.Paper.OrderedExchangeCoefficientComparison)
