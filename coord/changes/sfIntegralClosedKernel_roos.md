# WeilConjectures.sfIntegralClosedKernel_roos

## Reason

Split one genuine operation-comparison step from the realization theorem. The original
realization signature and every existing definition remain unchanged. This theorem
introduces no chosen data or new definition. Its only consumer is the proof of the
assigned item; its corresponding node records the source and complete proof plan.

## Old

Absent: this is a new public theorem in a new module.

## New

```lean
theorem sfIntegralClosedKernel_roos
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsNoetherian X]
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hK : IsSfDerivedComplete l E X K)
    (hiK : IsSfDerivedComplete l E Z ((integralDerivedPullback l E i).obj K)) :
    letI : HasCountableProducts (DerivedCategory (scalarReductionSource.{u, u} l E X)) :=
      integralOperationsDerivedCountableProducts l E X
    ∃ L : SfIntegralDirectImage l E i ((integralDerivedPullback l E i).obj K),
      Nonempty ((sfRecollementModuleClosed l E i).mapDerivedCategory.obj K ≅ L.obj)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SfIntegralKernelRealization | D2 | Private proof import; supplies one vertex comparison. |

No existing target or definition changes meaning. There are no existing users of the
new name and no forced adaptations. The existing realization theorem is its sole
new consumer.

## Status

landed 20261025T100900-L-3633754 2026-10-25 (merge of deliver/D2/Sheaf.Paper.SfIntegralKernelRealization)
