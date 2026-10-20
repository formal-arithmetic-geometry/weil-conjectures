# AlgebraicGeometry.Scheme.OrderedExchange.reductionComplexCounit

## Reason

Use the existing generic model-data complex counit. Its factors are precisely
the homotopy quotient comparison, universal counit and homotopy-functor comparison
used by the former body. This keeps the representative normalization while
avoiding repeated expansion of concrete sheafification and localization data.
The change is coupled to the canonical choice of the bundled universal model.

## Old

```lean
def reductionComplexCounit (T : Scheme.{t})
    (P : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ) :
    (reduction d T).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((reductionModule d T).mapHomologicalComplex (.up ℤ)).obj P) :=
  AlgebraicGeometry.Scheme.reductionComplexCounit (reductionModule d T)
    (reduction d T) (reductionCounit d T) P
```

## New

```lean
def reductionComplexCounit (T : Scheme.{t})
    (P : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ) :
    (reduction d T).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((reductionModule d T).mapHomologicalComplex (.up ℤ)).obj P) :=
  (reductionData d T).complexCounit P
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | unclaimed | Same canonical reduction and representative equations; replace the expanded derived-limit complex unit by the existing library API, with its exact original formula proved generically, to repair compile time. |
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
