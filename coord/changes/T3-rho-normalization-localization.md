# AlgebraicGeometry.Scheme.OrderedExchange.RhoNormalization

## Reason

The original direct formula made the generic derived comparison repeatedly unfold
localization maps while checking its specialization. Its kernel check alone took about
28 seconds, and the full module with both new proofs exceeded the fixed 60-second limit.
Retain the completed reduction, its actual universal counit and its properties together
in the existing `DerivedReductionModelData` interface. `ModelPullNormalized` then states
the same complex-counit equation. Its K-flat and termwise-flat assumptions are paired in
a conjunction. No condition on the comparison or its models is weakened or added.
The rho kernel check drops to about 14 seconds with this presentation.

The equivalence with the old formula follows by unfolding `ModelPullNormalized` and:

1. `DF.reduction` is the recorded `completedReductionTower T d`.
2. `DF.complexCounit P` is `completedReductionTowerComplexCounit T d P`: both use
   `coherenceReductionTowerCounit T d` and the same four localization-factor maps.
3. `(reductionData d T).complexCounit P` is `reductionComplexCounit d T P`.
4. `res`, `exchangeTowerRes`, `reduction` and
   `completedReductionComplexTowerFunctor` are the corresponding named presentations
   of the generic functors and maps.
5. A function on `KFlat P ∧ FlatTerms P` is equivalent to a function with the two
   curried hypotheses. The constant-tower localization selected in the body is the
   standard instance already used by the fixed target reduction data; the prior direct
   formula with this instance and its old body were checked by `Iff.rfl`.

The record contains only the existing functor and counit, with named theorems supplying
its proof fields. It chooses no additional object.

## Old

```lean
def RhoNormalization (T : Scheme.{t})
    (e : completedReductionTower T d ⋙ exchangeTowerRes d T ≅
        res d T ⋙ reduction d T) : Prop :=
  ∀ P : CochainComplex (reductionModules T (d.completedRing T)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
          (R := d.completedRing T) P →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
          (R := d.completedRing T) (P.X n)) →
        e.hom.app (DerivedCategory.Q.obj P) ≫
            (reduction d T).map
              ((reductionRestrict T (exchangeScalar d T)).mapDerivedCategoryFactors.hom.app P) ≫
            reductionComplexCounit d T
              (((reductionRestrict T (exchangeScalar d T)).mapHomologicalComplex (.up ℤ)).obj P) =
          (exchangeTowerRes d T).map (completedReductionTowerComplexCounit T d P) ≫
            (exchangeTowerModuleRes d T).mapDerivedCategoryFactors.hom.app
              ((completedReductionComplexTowerFunctor T d).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (ordinaryRho d T).symm (.up ℤ)).hom.app P)
```

## New

```lean
def RhoNormalization (T : Scheme.{t})
    (e : completedReductionTower T d ⋙ exchangeTowerRes d T ≅
        res d T ⋙ reduction d T) : Prop :=
  letI := exchangeTowers_hasDerived T (exchangeConstantRing T A)
  let DF : DerivedReductionModelData (completedReductionModuleTowerFunctor T d)
      (fun P ↦ CochainComplex.IsKFlatIndependentCoefficients (R := d.completedRing T) P ∧
        ∀ n : ℤ, SheafOfModules.IsFlatOnSite
          (J := ProEt.topology T) (R := d.completedRing T) (P.X n)) :=
    { reduction := completedReductionTower T d
      counit := coherenceReductionTowerCounit T d
      isLeftDerived := (completedReductionTower_properties T d).1
      isIso_counit := fun P hP ↦ (completedReductionTower_properties T d).2.2 P hP.1 }
  ModelPullNormalized (completedReductionModuleTowerFunctor T d) (reductionModule d T)
    (reductionRestrict T (exchangeScalar d T)) (exchangeTowerModuleRes d T)
    DF (reductionData d T) (ordinaryRho d T).symm e
```

## Users

`tools/downstream.py Sheaf.Paper.OrderedExchangeCoefficientComparison --uses RhoNormalization`
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

Validation: the generic presentation equivalence and both concrete counit identities
compiled together in 53.9 seconds. The concrete source identity is proved by `rfl`,
as is the target identity; the generic equivalence curries the conjunction and rewrites
these two identities. The final item compiled in 31.9 seconds, and all three unchanged
direct importers compiled against it (5.3, 7.2 and 26.2 seconds respectively).

## Status

landed 20261022T020117-L-34354 2026-10-22 (merge of deliver/T3/Sheaf.Paper.OrderedExchangeCoefficientComparison)
