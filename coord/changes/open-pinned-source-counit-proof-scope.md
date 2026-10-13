# OpenPinnedSourceCounitTriangle proof scope

## Reason

The completed proof uses six proved private helpers. Local transparency attributes
prevent expensive unfolding of the concrete sheaf and tensor-pullback constructions.
The static checker classifies the added `attribute` and `omit` commands as interface
changes, although their scope is local and all existing public signatures, visibility,
public imports, and definition bodies remain unchanged. A proof-only
`import all Sheaf.AlgebraicGeometry.AffineSpectrumCompositionCounitSquare`
reuses its existing private tensor composition symmetry theorem, without exporting
its private scope to clients.

## Old

The module had no local transparency attributes or omission commands. Its variables were:

```lean
variable [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
```

## New

The same variables remain verbatim. Generic private helpers omit those families of
instances when they do not use them. After the existing public definition, the module adds:

```lean
attribute [local irreducible] derivedPullback
attribute [local irreducible] Scheme.Modules.tensorPullbackCompositionIso
  Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] DerivedCategory
  Functor.mapHomologicalComplex HomotopyCategory Functor.mapHomotopyCategory
  HomotopyCategory.quotient DerivedCategory.Q DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh
```

Before the final theorem, it adds:

```lean
attribute [local irreducible] singleComplexOpenPullbackIso openPinnedTensorOpenIso
```

The final theorem uses a scoped `maxHeartbeats 400000` option. These commands affect
proof checking in this module only. No target or public statement changes. No dependent
module needs adaptation, and no semantic target review is reopened.

## Users

`tools/downstream.py` with `--uses open_pinned_source_counit_triangle
openPinnedHomotopySourceCompositionIso` reports these textual declaration users.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.OpenPinnedSourceCounitTriangle | J4 | proof checking only |
| Sheaf.AlgebraicGeometry.OpenPinnedCounitHomotopyRestriction | unclaimed | no interface change |
| Sheaf.AlgebraicGeometry.OpenPinnedTensorCounitTransport | S2 | no interface change |

No module other than the assigned item is adapted.

## Status

landed 20261013T201756-L-3972041 2026-10-13 (merge of deliver/J4/Sheaf.AlgebraicGeometry.OpenPinnedSourceCounitTriangle)
