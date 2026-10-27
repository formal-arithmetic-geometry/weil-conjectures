# WeilConjectures.VerdierHomChainComposition.stage_specialization

## Reason

The abstract `VerdierExchange.StageData` supplies an objectwise family of projection
isomorphisms without a naturality field. The old first conjunct claimed naturality
of the entire chain for every such family, so it was false. For identity operations
on a characteristic-zero point, fix the projection at the one-dimensional
representing object and multiply its component at a two-dimensional test object by
-1. The identity-test inverseComponent stays fixed while the chain on a nonzero
map from that test to the unit changes sign.

Require precisely projection naturality in the test object. This law holds for
the canonical projection in the node and is used explicitly to move the arbitrary
test arrow through the chain. No definition, target, or geometric composition or
identity theorem changes. The repaired theorem is proved, not left as a new hole.

## Old

```lean
theorem stage_specialization (M : C l Ω X t) :
    (∀ (N T : C l Ω Y t) (v : T ⟶ d.homY.obj (op (F.F.obj M), N)),
      stageChain l Ω d M N T v =
        v ≫ (stageModel l Ω d).inverseComponent l Ω M N) ∧
    (∀ h : TensorAdjunctionExchange.Conclusion l Ω (stageModel l Ω d),
      ∀ N : C l Ω Y t,
        (h.exchange.inv.app (op M)).app N = stageChain l Ω d M N _ (𝟙 _)) ∧
    d.epsilon l Ω M =
      stageChain l Ω d M (A.G.obj unit) _ (𝟙 _) ≫
        d.star.map (d.homX.map (Prod.mkHom (𝟙 (op M)) d.dualizing.hom))
```

## New

```lean
theorem stage_specialization
    (projection_natural : ∀ (T T' : C l Ω Y t) (a : T ⟶ T') (M : C l Ω X t),
      F.F.map (d.closedX.tensor.map (Prod.mkHom (d.pull.map a) (𝟙 M))) ≫
          (d.projection T' M).hom =
        (d.projection T M).hom ≫
          d.closedY.tensor.map (Prod.mkHom a (𝟙 (F.F.obj M))))
    (M : C l Ω X t) :
    (∀ (N T : C l Ω Y t) (v : T ⟶ d.homY.obj (op (F.F.obj M), N)),
      stageChain l Ω d M N T v =
        v ≫ (stageModel l Ω d).inverseComponent l Ω M N) ∧
    (∀ h : TensorAdjunctionExchange.Conclusion l Ω (stageModel l Ω d),
      ∀ N : C l Ω Y t,
        (h.exchange.inv.app (op M)).app N = stageChain l Ω d M N _ (𝟙 _)) ∧
    d.epsilon l Ω M =
      stageChain l Ω d M (A.G.obj unit) _ (𝟙 _) ≫
        d.star.map (d.homX.map (Prod.mkHom (𝟙 (op M)) d.dualizing.hom))
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.VerdierHomChainComposition | Y7 | Owning module; corrected theorem is proved from projection naturality. No other declaration uses it. |

`tools/downstream.py Sheaf.Paper.VerdierHomChainComposition --uses
WeilConjectures.VerdierHomChainComposition.stage_specialization` reports no downstream
modules and only the defining module as a textual use. A DAG scan finds the parent
`fix-prop-coherence`, whose canonical geometric projection is already natural;
this abstract-presentation correction leaves the parent's mathematical assertion
and the main geometric theorem unchanged. No target statement uses this theorem
or a changed definition. No forced adaptation is needed.

## Status

landed 20261025T164900-L-1118754 2026-10-25 (merge of deliver/Y7/Sheaf.Paper.VerdierHomChainComposition)
