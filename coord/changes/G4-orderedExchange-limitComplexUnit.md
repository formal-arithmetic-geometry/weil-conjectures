# AlgebraicGeometry.Scheme.OrderedExchange.limitComplexUnit

## Reason

The unmodified `Sheaf.Paper.OrderedExchangeCoefficientComparison` exceeded the
60-second compile limit against the repaired reduction interface. Replace its
expanded complex-unit construction by the existing library API
`Functor.rightDerivedFunctorUnitQ`. The private proved generic
`complexUnit_formula` identifies this API with exactly the original four-factor
formula: the omitted factor is Qh applied to an identity. No derived functor,
unit normalization, target meaning, statement signature or visibility changes.
The module is unclaimed. The added public source import is needed by the body
of this public definition; no adopted source declaration is modified.

## Old

```lean
def limitComplexUnit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (P : CochainComplex (exchangeTowers T R) ℤ) :=
  (DerivedCategory.quotientCompQhIso _).inv.app
      (((completedTowerLimit T R).mapHomologicalComplex (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((completedTowerLimit T R).mapHomotopyCategoryFactors (.up ℤ)).inv.app P) ≫
    (completedTowerLimit T R).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj P) ≫
    (completedRlim T R).map ((DerivedCategory.quotientCompQhIso _).hom.app P)
```

## New

```lean
def limitComplexUnit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (P : CochainComplex (exchangeTowers T R) ℤ) :=
  (completedTowerLimit T R).rightDerivedFunctorUnitQ P
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | unclaimed | The same ordinary complex unit, as proved by the generic compatibility formula; all existing limit/scalar normalization statements remain unchanged. |

`tools/downstream.py --uses limitComplexUnit` reports only that module.
The existing unit is equal to the new one by `complexUnit_formula` specialized
to `completedTowerLimit T R`, not merely isomorphic or an arbitrary choice.
This repair itself changes no target meaning. The other changed definitions in
this packet independently reopen target meaning review as recorded there.
No target signature is changed.

## Status

landed 20261020T221158-L-4154121 2026-10-20 (merge of deliver/G4/Sheaf.Paper.ProEtaleConstantReductionTower)
