# AlgebraicGeometry.derivedLocallyBoundedBelowGlobal

## Reason

The stage-3 queue assigns retirement of the Sheaf duplicate. The same named theorem,
with the same mathematical statement and complete finite-cover proof, already exists in
WeilConjectures.AlgebraicGeometry.DerivedLocallyBoundedBelowGlobal. The source version
spells out the overFunctor universe as .{u}; the Sheaf version infers it. A compiled
compatibility example applies the upstream theorem to the original Sheaf signature.
Keep the upstream declaration verbatim and withdraw the unused Sheaf declaration.

## Old

In Sheaf.AlgebraicGeometry.DerivedLocallyBoundedBelowGlobal:

```lean
theorem derivedLocallyBoundedBelowGlobal (Y : Scheme.{u}) [IsNoetherian Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : schemeDerivedCategory Y)
    (hlocal : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ ∃ a : ℤ, ∀ n : ℤ, n < a →
      IsZero ((SheafOfModules.overFunctor (moduleRings Y.toRingedSpace) U).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj E))) :
    ∃ a : ℤ, E.IsGE a
```

## New

The Sheaf module is withdrawn as an empty module, with no declarations or imports.
The existing DAG node is attached to the already proved upstream declaration:

```lean
theorem derivedLocallyBoundedBelowGlobal (Y : Scheme.{u}) [IsNoetherian Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : schemeDerivedCategory Y)
    (hlocal : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ ∃ a : ℤ, ∀ n : ℤ, n < a →
      IsZero ((SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) U).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj E))) :
    ∃ a : ℤ, E.IsGE a
```

No upstream signature, proof, attribute, public import, or definition is changed.
No target statement or definition changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DerivedLocallyBoundedBelowGlobal | W4 | Withdraw the unused duplicate. |
| WeilConjectures.AlgebraicGeometry.PseudoCoherentRHomQuasiCoherent | unclaimed | Already imports the upstream module and uses its theorem; no adaptation. |

Source search and tools/downstream.py report zero downstream modules of the Sheaf
module. The sole external theorem call is in the upstream consumer named above.
It already uses the upstream import, so there are no affected caller interfaces or
forced adaptations. Its existing source is compiled unchanged during verification.

## Status

landed 20261020T135437-L-1824282 2026-10-20 (merge of deliver/W4/Sheaf.AlgebraicGeometry.DerivedLocallyBoundedBelowGlobal)
