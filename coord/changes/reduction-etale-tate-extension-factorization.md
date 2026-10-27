# AlgebraicGeometry.ProEtale.reductionEtaleTateExtensionMap

## Reason

The direct concrete adjunction transpose is expensive for Lean's kernel to check.
Factor it through the existing generic scalar-single comparison, followed by the
ordinary scalar-extension transpose of the same generator-normalized sheaf map.
The private generic theorem `reductionFactoredTranspose` proves equality with
the old formula without a flatness assumption, specialized to ordinary scalar
extension/restriction, derived scalar extension/restriction, the two single
functors, the scalar adjunctions and the exact-restriction single comparison. The public signature is unchanged.
This preserves the Tate map and every statement that uses it; the target statements
remain verbatim. The definition used in their dependency closure is recorded here
for independent review.

## Old

```lean
def reductionEtaleTateExtensionMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    (Etale.scalarExtension φ T).obj (Etale.ordinaryFiniteLine A N hA T) ⟶
      Etale.ordinaryFiniteLine B N hB T :=
  ((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars.{u} T.smallEtaleTopology φ)).homEquiv _ _).symm
    ((DerivedCategory.singleFunctor _ 0).map (reductionEtaleTateMap φ T N hA hB) ≫
      ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategorySingleFunctor
        0).inv.app (finiteEtaleTateLine T N B hB))
```

## New

```lean
def reductionEtaleTateExtensionMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    (Etale.scalarExtension φ T).obj (Etale.ordinaryFiniteLine A N hA T) ⟶
      Etale.ordinaryFiniteLine B N hB T :=
  WeilConjectures.PurityFiniteSetting.purityScalarSingleMap φ T
      (finiteEtaleTateLine T N A hA) ≫
    (DerivedCategory.singleFunctor _ 0).map
      (((etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _).symm
        (reductionEtaleTateMap φ T N hA hB))
```

## Users

`tools/downstream.py Sheaf.SecSmoothPurity.ReductionExceptional --uses
reductionEtaleTateExtensionMap` reports one module using the declaration. There are
64 transitive importers, but none refers to this declaration directly outside its
own module. The two external users of the chart comparison built from this map are
also listed below.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SecSmoothPurity.ReductionExceptional | D3 | Same signature and map; prove equality with the original transpose and its invertibility. |
| Sheaf.Paper.RawChartScalarCounitPasting | P6 | Uses the chart scalar isomorphism; its statement retains the same canonical map. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Uses the chart scalar isomorphism; its statement retains the same canonical map. |

No consumer source adaptation is required: the underlying map is propositionally
equal, and existing consumers do not unfold the Tate extension map.

## Status

landed 20261025T013909-L-4031890 2026-10-25 (merge of deliver/D3/Sheaf.SecSmoothPurity.ReductionExceptional)
