# AlgebraicGeometry.sheafExt_isCoherent

## Reason

Restore the assigned quarantined item and repair its missing public statement import.
The archived source gives `unknown constant AlgebraicGeometry.RingedSpace.IsCoherent`
for all three occurrences in its public theorem signature. The compiler identifies
`WeilConjectures.AlgebraicGeometry.Coherent` as privately imported.

## Old

```lean
import WeilConjectures.AlgebraicGeometry.Coherent
```

The unchanged public signature is:

```lean
theorem sheafExt_isCoherent (X : Scheme.{u₁}) [IsLocallyNoetherian X]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    (F G : SheafOfModules.{u₁} (moduleRings X.toRingedSpace))
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) :
    ∀ q : ℤ, RingedSpace.IsCoherent X.toRingedSpace (moduleSheafExt X q F G)
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.Coherent
```

The theorem signature above is preserved verbatim. Its original `sorry` is replaced
by a proof. All added helpers are private, proved, and appear only in proof bodies.
No definition, predicate, instance, target signature, or source-library file changes.
The quarantine archive and DAG Lean attachment are preserved.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.SheafExtCoherent --uses sheafExt_isCoherent`
reports `unknown module(s)` because the current source is quarantined. A text search
of both `lean/` and `quarantine/` finds only the quarantined importer below and the
assigned archive itself, with no other direct declaration use.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SheafExtCoherent | G1 | Restored; public import repaired; theorem proved with same statement. |
| Sheaf.AlgebraicGeometry.ExtSupportCohomologyVanishing | quarantined; not adapted | Same theorem signature and definitions; restored module now exports the predicate its signature requires. |

There are no changed mathematical meanings, including in any transitive target.
No consumer adaptation is forced by this additive public import.

## Status

landed 20261021T152312-L-1858696 2026-10-21 (merge of deliver/G1/Sheaf.AlgebraicGeometry.SheafExtCoherent)
