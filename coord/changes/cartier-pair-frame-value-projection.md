# cartierPairFrameVal

## Reason

Expose the underlying isomorphism directly, so proof checking does not repeatedly
synthesize the two invertibility instances before projecting the frame. The
original `etaleIsoTorsorVal` is itself defined by `x.down.1`, so this is a
definitional equality and preserves the type and the actual morphism. The torsor
construction is unchanged. Locally freezing the frame interfaces in the two large
proofs then lets their proved value, naturality and scalar APIs control unfolding.

## Old

```lean
def cartierPairFrameVal {D T : Scheme.{u}} (i : D ⟶ T) (hI : i.ker.IsInvertible)
    {U : T.Etaleᵒᵖ} (x : (cartierPairFrameTorsor i hI).sheaf.obj.obj U) :
    (Scheme.Modules.pullback U.unop.hom).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback U.unop.hom).obj (Scheme.Modules.dual i.ker.toModules) :=
  letI := hI.isInvertible_dual_toModules
  letI := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    (Scheme.Modules.dual i.ker.toModules)
  Scheme.Modules.etaleIsoTorsorVal (Scheme.Modules.dual i.ker.toModules) x
```

## New

```lean
def cartierPairFrameVal {D T : Scheme.{u}} (i : D ⟶ T) (hI : i.ker.IsInvertible)
    {U : T.Etaleᵒᵖ} (x : (cartierPairFrameTorsor i hI).sheaf.obj.obj U) :
    (Scheme.Modules.pullback U.unop.hom).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback U.unop.hom).obj (Scheme.Modules.dual i.ker.toModules) :=
  x.down.1
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CartierPairTensorAddition | G2 | Uses the unchanged frame-value API. |

`tools/downstream.py Sheaf.AlgebraicGeometry.CartierPairTensorAddition --uses
cartierPairFrameVal` reports only this module as using the definition. It lists
`Sheaf.Paper.RamifiedCartierSupportedPurity` as an importer but finds no use of
`cartierPairFrameVal` there. No other module needs adaptation. Public signatures
and visibility are identical.

## Status

landed 20261025T003320-L-3227535 2026-10-25 (merge of deliver/G2/Sheaf.AlgebraicGeometry.CartierPairTensorAddition)
