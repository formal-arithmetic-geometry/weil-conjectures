# AlgebraicGeometry.Scheme.OrderedExchange.ReductionPullNormalized

## Reason

Share the generic normalization predicate `ConstantPerfectProjection.PullNormalized`
between the derived descent proof and the finite-level perfect projection lemma.
Expanding this predicate gives exactly the former representative formula, with
the same quantification over all K-flat complexes. The proof and the public
interface previously compared two large expanded terms; the shared predicate
prevents this repeated unfolding. The combined item compiled in 36.1 seconds
after the repair; the earlier expanded versions exceeded the 60-second limit.
The generic predicate is placed below both consumers to avoid an import cycle,
not to split a file or proof to meet the compile limit.

## Old

```lean
def ReductionPullNormalized
    (τ : reduction d V ⋙ exchangeConstantPull (A := A) f ≅
        pull (A := A) f ⋙ reduction d U) : Prop :=
  ∀ P : CochainComplex (reductionModules V (exchangeConstantRing V A)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := exchangeConstantRing V A) P →
        τ.hom.app (DerivedCategory.Q.obj P) ≫
            (reduction d U).map
              ((proEtaleRingDerivedPullbackFactors f
                (exchangeConstantRing V A) (exchangeConstantRing U A)
                (exchangeConstantIso f A)).hom.app P) ≫
            reductionComplexCounit d U
              (((proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
                (exchangeConstantIso f A)).mapHomologicalComplex (.up ℤ)).obj P) =
          (exchangeConstantPull (A := A) f).map (reductionComplexCounit d V P) ≫
            (exchangeTowerModulePull f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).mapDerivedCategoryFactors.hom.app
              (((reductionModule d V).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (ordinaryReductionPullIso d f)
                (.up ℤ)).hom.app P)
```

## New

```lean
def ReductionPullNormalized
    (τ : reduction d V ⋙ exchangeConstantPull (A := A) f ≅
        pull (A := A) f ⋙ reduction d U) : Prop :=
  ConstantPerfectProjection.PullNormalized (reductionModule d V) (reductionModule d U)
    (proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A))
    (exchangeTowerModulePull f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A))
    (reductionData d V) (reductionData d U) (ordinaryReductionPullIso d f) τ
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | unclaimed | No direct use of this declaration; derived-limit complex-unit construction adapted for compile time in the same packet. |
| Sheaf.Paper.ProEtaleConstantReductionTower | G4 | Same universal constructions and normalized maps; proofs updated. |

This table includes every textual hit from `tools/downstream.py --uses`;
name collisions are identified above. No adopted source-library file is changed. Direct
importers and the coefficient-comparison consumer are checked against the new
module. Statements involving the repaired universal pair retain their intended
meaning: the constant coefficient rings, finite quotients, strict transitions,
universal properties, normalizing equations and completion unit are unchanged.
Any target whose statement depends on a changed definition must undergo the
required statement review again. No target signature is changed.

## Status

landed 20261020T221158-L-4154121 2026-10-20 (merge of deliver/G4/Sheaf.Paper.ProEtaleConstantReductionTower)
