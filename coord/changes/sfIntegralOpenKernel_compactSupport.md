# WeilConjectures.sfIntegralOpenKernel_compactSupport

## Reason

Split one genuine operation-comparison step from the realization theorem. The original
realization signature and every existing definition remain unchanged. This theorem
introduces no chosen data or new definition. Its only consumer is the proof of the
assigned item; its corresponding node records the source and complete proof plan.

## Old

Absent: this is a new public theorem in a new module.

## New

```lean
theorem sfIntegralOpenKernel_compactSupport
    (k : Type u) [Field k] (hk : IsUnit (l : k))
    {Z U X : Scheme.{u}}
    [X.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [j.IsOver (Spec (.of k))]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (K : sfIntegralConstructibleCategory l E X)
    (h : sfIntegralConstructible l E U ((integralDerivedPullback l E j).obj K.obj)) :
    letI := sfRecollementNoetherian k X
    letI := (sfRecollementOpenFiniteType k j).1
    letI := (sfRecollementOpenFiniteType k j).2.1
    letI := (sfRecollementOpenFiniteType k j).2.2
    Nonempty ((sfRecollementModuleOpen l E i).mapDerivedCategory.obj K.obj ≅
      (sfIntegralCompactSupportValue l E k hk
        (Compactification.ofIsOpenImmersion j) ⟨_, h⟩).obj)
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
