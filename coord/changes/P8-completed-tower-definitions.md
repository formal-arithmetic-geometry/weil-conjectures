# AlgebraicGeometry.Scheme.AdicCoefficientDatum.fourTowerCorners

## Reason

Separate the existing strict tower definitions from their compatibility proof. The existing
stronger strict-tower mate normalization theorem contains exactly the evaluation clause and
already proves naturality. Its only import path to the compatibility module runs through
CompletedBaseChangeMap, which uses the definitions and never the compatibility theorem.
Keeping definitions and theorem together prevents using this existing result.
This extraction removes that artificial import cycle; it is not a split to avoid a compile
limit. No mathematical definition, signature, hypothesis, or target changes.

## Old

In `Sheaf.Paper.CompletedTowerCompatibility`:

```lean
/-- The strict four corner towers, formed before taking Rlim. The third corner uses
ordinary pullback. Source: blueprint tower compatibility
(blueprint: lem-weil-pbc-tower-compatibility). -/
def AdicCoefficientDatum.fourTowerCorners (K : d.derived X) :
    Fin 4 → DerivedCategory (d.towers Y') :=
  ![(d.towerPull g).obj ((completedReductionTower Y d).obj ((d.push f).obj K)),
    (d.towerPull g).obj ((d.towerPush f).obj
      ((completedReductionTower X d).obj K)),
    (completedReductionTower Y' d).obj ((d.push f').obj ((d.pull g').obj K)),
    (d.towerPush f').obj ((d.towerPull g').obj
      ((completedReductionTower X d).obj K))]

/-- The specified strict projection h, including the canonical source identification.
Source: blueprint tower compatibility (blueprint: lem-weil-pbc-tower-compatibility). -/
def AdicCoefficientDatum.towerH (K : d.derived X) :
    d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 0 ≅
      d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 1 :=
  (d.towerPull g).mapIso (asIso (d.towerProjection f K))

/-- The specified strict projection h', followed by the inverse pullback/reduction map.
Source: blueprint tower compatibility (blueprint: lem-weil-pbc-tower-compatibility). -/
def AdicCoefficientDatum.towerH' (K : d.derived X) :
    d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 2 ≅
      d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 3 :=
  asIso (d.towerProjection f' ((d.pull g').obj K)) ≪≫
    (d.towerPush f').mapIso ((d.reductionTowerPullbackIso g').symm.app K)

/-- The strict reduction of ambient exchange, with the source chi retained.
Source: blueprint tower compatibility (blueprint: lem-weil-pbc-tower-compatibility). -/
def AdicCoefficientDatum.towerV (K : d.derived X) :
    d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 0 ⟶
      d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 2 :=
  (d.reductionTowerPullbackIso g).hom.app ((d.push f).obj K) ≫
    (completedReductionTower Y' d).map ((d.integralExchange sq).app K)

/-- The specified strict lift of finite exchange. This is the projection-formula
realization H' R(e) H inverse; equality of its evaluations does not define its lift.
Source: blueprint tower compatibility, as expanded in strict-tower mate normalization
(blueprint: lem-weil-pbc-tower-compatibility). -/
def AdicCoefficientDatum.towerV' (K : d.derived X) :
    d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 1 ⟶
      d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 3 :=
  (d.towerH (f := f) (f' := f') (g := g) (g' := g') K).inv ≫
    d.towerV sq K ≫ (d.towerH' (f := f) (f' := f') (g := g) (g' := g') K).hom
```

`Sheaf.Paper.CompletedBaseChangeMap` publicly imports
`Sheaf.Paper.CompletedTowerCompatibility`.

## New

Exactly the same five declarations, including bodies and visibility, live in
`Sheaf.Paper.CompletedTowerCorners`. The old module publicly imports the new one and
proves the unchanged theorem. CompletedBaseChangeMap publicly imports the definition
module. No consumer of CompletedBaseChangeMap uses fourTowers_compatibility (the downstream declaration search finds only its own declaration). StrictTowerExchangeMateNormalization is
unchanged, including all its public signatures; it can now be imported without a cycle.
The two consumers' DAG statement citations and dependencies now name the definition node
rather than the former combined node. The compatibility statement also explicitly cites
the extracted construction. Their mathematical statements remain identical; the associated
statement_change records account for every existing citer.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompletedTowerCompatibility | P8 | Publicly reexports the unchanged definitions and proves its theorem. |
| Sheaf.Paper.CompletedBaseChangeMap | unclaimed | Imports the definition module; no use of compatibility. |
| Sheaf.Paper.StrictTowerExchangeMateNormalization | U7 | Uses the unchanged definitions via CompletedBaseChangeMap; no source adaptation. |
| Sheaf.Paper.QuotientCornerFrobeniusStructures | unclaimed | All five definitions retain identical signatures, bodies and visibility; no adaptation. |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | D5 | towerH and towerV' retain identical signatures, bodies and visibility; no adaptation. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | Y7 | towerH retains its signature, body and visibility; no adaptation. |
| Sheaf.Paper.CompleteProetale | S6 | Direct importer; all declarations remain publicly available; no adaptation. |
| Sheaf.Paper.CompletedMapReduction | R4 | Direct importer; all declarations remain publicly available; no adaptation. |
| Sheaf.Paper.PbcRectangleDerivedLimit | unclaimed | Direct importer; all declarations remain publicly available; no adaptation. |

The transitive import closure keeps all original names available. A source search found
no external use of `fourTowers_compatibility`; all actual uses of the five moved definitions
retain their original meanings and public availability. No target statement review is
reopened because the mathematical data is byte-for-byte identical.

## Status

landed 20261019T093539-L-2325287 2026-10-19 (merge of deliver/P8/Sheaf.Paper.CompletedTowerCompatibility)
