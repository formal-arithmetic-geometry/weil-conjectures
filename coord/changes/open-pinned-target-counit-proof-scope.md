# OpenPinnedTargetCounitTriangle proof scope

## Reason

The completed proof reuses the proved private `openCounit`, `compositionCounit`,
and `mappedHomotopyInvHom` helpers through a proof-only
`import all Sheaf.AlgebraicGeometry.OpenPinnedSourceCounitTriangle`.
Three proved private helpers supply target termwise cancellation and ordinary
category-theory algebra. Local transparency attributes keep sheaf and chosen
pullback constructions abstract while checking the final calculation. The static
checker treats these commands as interface changes, so this record documents their
local scope. Existing public signatures, visibility, public imports, and the
existing definition body are unchanged. No target meaning changes.

## Old

The module had no local transparency attributes, private helpers, or scoped
heartbeat option. Its existing variables were:

```lean
variable [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
```

## New

Those variables and both existing public declarations remain unchanged. After the
existing public definition the proof adds the following local attributes:

```lean
attribute [local irreducible] derivedPullback
attribute [local irreducible] Scheme.Modules.tensorPullbackCompositionIso
  Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] DerivedCategory
  Functor.mapHomologicalComplex HomotopyCategory Functor.mapHomotopyCategory
  HomotopyCategory.quotient DerivedCategory.Q DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh
attribute [local irreducible] singleComplexOpenPullbackIso openPinnedTensorOpenIso

```

Only the final theorem uses `set_option maxHeartbeats 400000 in`, to compare four
factorization equations involving selected localization functors. The wall-clock
compile limit is unchanged. These settings do not export to importing modules.

## Users

`tools/downstream.py` with `--uses open_pinned_target_counit_triangle
openPinnedHomotopyTargetCompositionIso` lists the following textual users. The
claim status is that of the supplied repository snapshot. None needs adaptation;
no public signature or construction changed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.OpenPinnedTargetCounitTriangle | P4 | proof checking only |
| Sheaf.AlgebraicGeometry.OpenPinnedCounitHomotopyRestriction | unclaimed | none |
| Sheaf.AlgebraicGeometry.OpenPinnedTensorComparisonCoherence | unclaimed | none |
| Sheaf.AlgebraicGeometry.OpenPinnedTensorCounitTransport | unclaimed | none |

No module other than the assigned item is edited.

## Status

landed 20261014T001728-L-2553360 2026-10-14 (merge of deliver/P4/Sheaf.AlgebraicGeometry.OpenPinnedTargetCounitTriangle)
