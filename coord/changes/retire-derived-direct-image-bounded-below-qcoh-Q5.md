# Sheaf.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh

## Reason

Complete the retirement assigned by coord/retire-items.tsv under the human's
2026-10-20 instruction in coord/changes/retire-sheaf-twins-20261020.md. The upstream
twin has the identical public theorem, fully proved. The copy has no current
importers, and its former consumer has already migrated upstream. Preserve the
mathematical dependency by pointing the node at the upstream theorem.

## Old

The withdrawn copy's public theorem signature, verbatim:

```lean
theorem schemeDerivedDirectImage_preserves_QCoh_of_isGE
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (a : ℤ) [E.IsGE a] :
    schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E)
```

It is declared in
`Sheaf.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh`.
The remaining declarations in that module are proved private helpers.

## New

The identical public signature above remains available from
`WeilConjectures.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh`, without
changing the upstream file. Node `lem-pc-derived-direct-image-bounded-below-qcoh`
now records that module, file and declaration as its existing Lean realization.
The duplicate Sheaf file is withdrawn with `deleted.txt`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh | Q5 | Withdraw the duplicate. |
| WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh | unclaimed | Already imports the upstream twin and applies the identical theorem; no edit. |

`tools/downstream.py` reports zero downstream modules for the Sheaf copy. A direct
search of both roots and quarantine confirms no current importers. The sole DAG
parent is `lem-pc-derived-direct-image-preserves-qcoh`; its existing attachment is
already the upstream consumer listed above. The former Sheaf consumer named in
the retirement row is absent. No forced adaptations are needed. No target type
or definition changes meaning, and the unit's route is retained.

Validation: the upstream theorem's printed axioms are exactly `propext`,
`Classical.choice`, and `Quot.sound`. Its import closure and the parent's closure
contain no Sheaf/upstream twin pair and do not contain the withdrawn module.
The parent is compiled separately with lcompile.py.

## Status

landed 20261020T211818-L-3505134 2026-10-20 (merge of deliver/Q5/Sheaf.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh)
