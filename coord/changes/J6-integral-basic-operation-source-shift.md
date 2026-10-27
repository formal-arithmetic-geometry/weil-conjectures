# WeilConjectures.IntegralSystemRealization.BasicShiftOperation.sourceShift

## Reason

The previous proper-image branch forced the kernel to compare the expanded
reduction-operation-total-limit component with the component of the composite
CommShift used by `basicIntegralPushShift`. Profiling found expensive normalization
of the derived-limit model; complete versions took over the 60-second limit.
The canonical composite component gives the same isomorphism and lets the complete
proof compile in 16.9 seconds before final import cleanup.

For proper image, evaluate the source shift using `basicIntegralPushShift`, which
is explicitly constructed from `reductionShift`, `systemPushShift`, and `limitShift`
by the composite CommShift instance. The component equation
`Functor.commShiftIso_comp_hom_app`, applied twice, yields
`L.map (S.map reductionShift.hom) ≫ L.map systemPushShift.hom ≫ limitShift.hom`.
Functoriality of `L.map` and associativity turn this into the old expression.
The generic calculation in the proved private `coherentTriple` helper performs
exactly this calculation, without unfolding any concrete derived functor.
No endpoint isomorphism is chosen and no constituent shift is replaced. The
pullback, open, and both tensor branches retain the original expression.
Thus zero, positive, and negative shifts and their Koszul/Roos normalization
are preserved. Properness witnesses do not enter the shift construction.

The public type is unchanged (the arguments are written as equivalent Pi binders).
No theorem signature, target text, public import, or unit route changes. This is
an equivalent presentation of a public definition in the target dependency
closure, so independent definition/statement review under stage 2 section 4
applies; no weakening of any target is intended or needed.

## Old

```lean
def BasicShiftOperation.sourceShift (o : GeneratorReduction.Operations l E)
    (A : BasicShiftOperation l E B U V) (r : ℤ) (K : Integral l E U.left) :
    (A.source l E o).obj (K⟦r⟧) ≅ ((A.source l E o).obj K)⟦r⟧ :=
  (coefficientSequenceLimit l E V.left).mapIso
    ((A.system l E o).mapIso
      ((Functor.commShiftIso _ (self := reductionShift l E U.left) r).app K) ≪≫
      A.systemShift l E o r ((calculus l E U.left).reduction.obj K)) ≪≫
    (Functor.commShiftIso _ (self := limitShift l E V.left) r).app
      ((A.system l E o).obj ((calculus l E U.left).reduction.obj K))
```

## New

```lean
def BasicShiftOperation.sourceShift (o : GeneratorReduction.Operations l E) :
    (A : BasicShiftOperation l E B U V) → (r : ℤ) → (K : Integral l E U.left) →
    (A.source l E o).obj (K⟦r⟧) ≅ ((A.source l E o).obj K)⟦r⟧
  | .push f _, r, K =>
      (Functor.commShiftIso _ (self := basicIntegralPushShift l E o f.left) r).app K
  | A, r, K =>
      (coefficientSequenceLimit l E V.left).mapIso
        ((A.system l E o).mapIso
          ((Functor.commShiftIso _ (self := reductionShift l E U.left) r).app K) ≪≫
          A.systemShift l E o r ((calculus l E U.left).reduction.obj K)) ≪≫
        (Functor.commShiftIso _ (self := limitShift l E V.left) r).app
          ((A.system l E o).obj ((calculus l E U.left).reduction.obj K))
```

## Users

`tools/downstream.py Sheaf.SixFunctors.IntegralBasicOperationShift --uses
BasicShiftOperation.sourceShift` lists the following downstream modules and two
textual matches besides the item. Both textual matches refer to
`IndependentExpression.sourceShift`, not this declaration. None unfolds or
uses the changed branch. Their statements therefore keep their meanings and
no adaptation is forced. All nine downstream claim files were absent when
checked; no consumer module is included or modified in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.IntegralBasicOperationShift | J6 | Equivalent proper source shift; proof completed |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed | No direct use of this definition; no adaptation |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | No direct use of this definition; no adaptation |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed | No direct use of this definition; no adaptation |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | No direct use of this definition; no adaptation |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | No direct use of this definition; no adaptation |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | No direct use of this definition; no adaptation |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed | No direct use of this definition; no adaptation |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | No direct use of this definition; no adaptation |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed | No direct use of this definition; no adaptation |

## Status

landed 20261025T204739-L-3003535 2026-10-25 (merge of deliver/J6/Sheaf.SixFunctors.IntegralBasicOperationShift)
