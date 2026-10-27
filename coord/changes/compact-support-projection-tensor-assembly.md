# WeilConjectures.CompactSupportPbcProjection.tensorComparisonArrow

## Reason

The kernel spent 25–34 seconds checking this concrete composite. Its three
category operations are now checked once on abstract categories in
`projectionTensorArrowAssembly`, then specialized to these actual functors and
arrows. Unfolding the new helper gives exactly the original three-arrow
composition. No target meaning, carrier, normalization or theorem signature
changes. This fixes expensive unfolding rather than splitting the file or
raising the limit.

## Old

```lean
def tensorComparisonArrow
    (R : WfTensorCompletion.RationalComparison D C Y₀ E₀)
    (hR : R.Normalized D C Y₀ E₀) (K L : WeilD D C Y₀ E₀) :
    (CompactSupportCoefficientTensor.rational D C Y₀ E₀ F WY).obj
        ((CompactSupportCoefficientTensor.rationalTensor D C Y₀ E₀).obj
          (((CompactSupportPbcTransport.pairInverse D C Y₀ E₀ F WY).obj K).carrier,
            ((CompactSupportPbcTransport.pairInverse D C Y₀ E₀ F WY).obj L).carrier)) ⟶
      R.completed.obj (K.carrier, L.carrier) :=
  (CompactSupportCoefficientTensor.comparison D C Y₀ E₀ F WY R hR).hom.app
            (((CompactSupportPbcTransport.pairInverse D C Y₀ E₀ F WY).obj K).carrier,
              ((CompactSupportPbcTransport.pairInverse D C Y₀ E₀ F WY).obj L).carrier) ≫
          R.ordinary.map (Prod.mkHom
            (CompactSupportPbcTransport.cancellation D C Y₀ E₀ F WY K).hom
            (CompactSupportPbcTransport.cancellation D C Y₀ E₀ F WY L).hom) ≫
          R.chi.hom.app (K.carrier, L.carrier)
```

## New

```lean
def tensorComparisonArrow
    (R : WfTensorCompletion.RationalComparison D C Y₀ E₀)
    (hR : R.Normalized D C Y₀ E₀) (K L : WeilD D C Y₀ E₀) :
    (CompactSupportCoefficientTensor.rational D C Y₀ E₀ F WY).obj
        ((CompactSupportCoefficientTensor.rationalTensor D C Y₀ E₀).obj
          (((CompactSupportPbcTransport.pairInverse D C Y₀ E₀ F WY).obj K).carrier,
            ((CompactSupportPbcTransport.pairInverse D C Y₀ E₀ F WY).obj L).carrier)) ⟶
      R.completed.obj (K.carrier, L.carrier) :=
  projectionTensorArrowAssembly
    (CompactSupportCoefficientTensor.rationalTensor D C Y₀ E₀)
    (CompactSupportCoefficientTensor.rational D C Y₀ E₀ F WY)
    R.ordinary R.completed
    (CompactSupportCoefficientTensor.comparison D C Y₀ E₀ F WY R hR) R.chi
    (((CompactSupportPbcTransport.pairInverse D C Y₀ E₀ F WY).obj K).carrier)
    (((CompactSupportPbcTransport.pairInverse D C Y₀ E₀ F WY).obj L).carrier)
    K.carrier L.carrier
    (CompactSupportPbcTransport.cancellation D C Y₀ E₀ F WY K).hom
    (CompactSupportPbcTransport.cancellation D C Y₀ E₀ F WY L).hom
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompactSupportProjectionFormula | F4 | Same explicit composite through generic assembly. |

`tools/downstream.py Sheaf.Paper.CompactSupportProjectionFormula --uses
tensorComparisonArrow` reports only this module. No external consumer adaptation
is required. The new helper is a public definition because it occurs in the body
of this public definition; its module is therefore a public import.

## Status

landed 20261025T201914-L-2644369 2026-10-25 (merge of deliver/F4/Sheaf.Paper.CompactSupportProjectionFormula)
