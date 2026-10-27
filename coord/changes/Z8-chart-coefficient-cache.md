# AlgebraicGeometry.Etale.ordinaryFiniteP1DiagonalChartMap

## Reason

The returned packet had replaced the chart body with a generic construction.
Current F1 instead records the same canonical composite as
`ordinaryFiniteChartTransport`. This repair preserves F1's body verbatim and
compares it to the generic construction only inside a proved private helper in
`OrdinaryFiniteDiagonalChartExchange`.

## Old

```lean
def ordinaryFiniteP1DiagonalChartMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    ordinaryFiniteP1DiagonalTarget A N hA S a ⟶
      (ordinaryFinitePushforward A
        (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).obj
          ((ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧) :=
  let e := (projectiveLineDiagonalChart S a).val
  let p := projectiveLineDiagonalProjection S a
  let L := (ordinaryFiniteLine A N hA
    (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧
  ordinaryFiniteChartTransport A e.hom p
    (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)
    (projectiveLineDiagonalChart S a).property L _
      (ordinaryFiniteShiftedLinePullback A N hA t e.hom
        ((map_natCast
          ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom N) ▸
          hS.map ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom)).hom
```


Current main defines `ordinaryFiniteP1DiagonalChartMap` by
`ordinaryFiniteChartTransport A e.hom p r hr L _ v`, where `v` is the normalized
shifted-line pullback comparison. The transport is the pushed adjunction unit,
derived direct-image compositor, equality comparison and pushed coefficient map,
in that order.

## New

```lean
def ordinaryFiniteP1DiagonalChartMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    ordinaryFiniteP1DiagonalTarget A N hA S a ⟶
      (ordinaryFinitePushforward A
        (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).obj
          ((ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧) :=
  let e := (projectiveLineDiagonalChart S a).val
  let p := projectiveLineDiagonalProjection S a
  let L := (ordinaryFiniteLine A N hA
    (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧
  ordinaryFiniteChartTransport A e.hom p
    (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)
    (projectiveLineDiagonalChart S a).property L _
      (ordinaryFiniteShiftedLinePullback A N hA t e.hom
        ((map_natCast
          ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom N) ▸
          hS.map ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom)).hom
```


The same body moves verbatim into `OrdinaryFiniteP1DiagonalComponents`, together
with `ordinaryFiniteChartTransport` and F1's complete component formula proof.
No chart-construction data changes. ChartExchange imports the separate
`ordinaryFiniteDiagonalChartMap_eq_generic` identification lemma and applies
the generic chart-pasting identity through that equality. The new theorem's
statement only identifies the two constructions for the same selected chart.
Its proof is the constructor-equation argument documented there; its final
functor-alias conversion remains a named theorem hole after repeated compile
timeouts. The main exchange-pasting calculation itself is complete.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DiagonalComponents` | Z8 | Retains F1's exact chart body and transport. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteDiagonalChartExchange` | Z8 | Compares the named transport with the generic transport in its private helper. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DiagonalTriangles` | Z8 | Retains the chart map and uses F1's named supported realization. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalData` | unclaimed | Retains its chart-pushforward construction. |
| `Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula` | F1 | Re-exports the complete relocated proof and constructions. |
| `Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals` | unclaimed | Same canonical chart map. |
| `Sheaf.AlgebraicGeometry.FiniteP1DiagonalChernComponents` | unclaimed | Same canonical chart map. |
| `Sheaf.Paper.TowerP1KernelScalarData` | unclaimed | Same canonical chart map. |

## Status

landed 20261027T135451-L-3711227 2026-10-27 (merge of deliver/Z8/Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DiagonalUnit)
