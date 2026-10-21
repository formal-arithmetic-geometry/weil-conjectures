# SheafOfModules.StrictQuotientExchange.strictQuotientExchangeUnitEquation

## Reason

The proof uses local irreducibility attributes to prevent elaboration from
unfolding derived-category localization, total complexes and normalized comparison
maps during categorical diagram calculations. This keeps the proof within the
unchanged 60-second compilation limit. Two local transparency options repeat the
existing file-level options. The static checker conservatively flags these commands
as an interface change and requests this record.

All attributes are local to this file. Importers retain the same reducibility
attributes, declaration signatures, public imports and definition bodies. Only
proofs and private proof imports change. No target meaning changes, and no
consumer requires adaptation. The unit-route private import
`Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison` is retained.

## Old

The theorem signature, verbatim, before the proof:

```lean
theorem strictQuotientExchangeUnitEquation
    (s : RingedTensorSquare S T X Y g f e h)
    (q : Coefficients f g h e s)
    (hperfect : HasPerfectLevels S q.atS.Q)
    (hf : IsIso f.ringMap) (hg : IsIso g.ringMap)
    (hh : IsIso h.ringMap) (he : IsIso e.ringMap)
    (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh)
    (jX : ConstantLimit X lX) (jY : ConstantLimit Y lY) :
    FullEquation q ag ah jX jY
```

There were no local irreducibility attributes following `FullEquation`.

## New

The following local proof-elaboration commands follow the unchanged definition
`FullEquation`:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] DerivedCategory.Q HomologicalComplex₂.total
  HomologicalComplex.mapBifunctorMap CochainComplex.kInjectiveResolutionFunctor
  CochainComplex.toKInjectiveResolution
attribute [local irreducible] total evComparison exactLeft firstProjection
  secondProjection conjugate limitComparison gamma evaluatedSource evaluatedTarget
  forgetQuotient RingedTensorSquare.exchange RingedTensorSquare.derivedComparison
```

The theorem signature is unchanged:

```lean
theorem strictQuotientExchangeUnitEquation
    (s : RingedTensorSquare S T X Y g f e h)
    (q : Coefficients f g h e s)
    (hperfect : HasPerfectLevels S q.atS.Q)
    (hf : IsIso f.ringMap) (hg : IsIso g.ringMap)
    (hh : IsIso h.ringMap) (he : IsIso e.ringMap)
    (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh)
    (jX : ConstantLimit X lX) (jY : ConstantLimit Y lY) :
    FullEquation q ag ah jX jY
```

## Users

`tools/downstream.py Sheaf.Paper.StrictQuotientExchangeUnitEquation --uses
SheafOfModules.StrictQuotientExchange.strictQuotientExchangeUnitEquation` finds
zero downstream modules and only the item's own declaration occurrence. The item
remains needed by the unfinished DAG parents; none of them is edited or withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.StrictQuotientExchangeUnitEquation | E3 | Local proof elaboration only; no signature or definition changes |

## Status

landed 20261021T162110-L-274539 2026-10-21 (merge of deliver/E3/Sheaf.Paper.StrictQuotientExchangeUnitEquation)
