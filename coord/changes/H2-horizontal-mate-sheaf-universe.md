# schemeDerivedBaseChange_horizontal_mate

## Reason

Restore the assigned module from the quarantine archive recorded in `coord/rework.tsv`.
Its section-level derived-category hypothesis omitted the module-value universe of
`SheafOfModules`. Elaboration consequently tried to identify
`Category.{u + 1, u + 1} AddCommGrpCat` with `Category.{u, u + 1} AddCommGrpCat`,
forcing the impossible equation `u + 1 = u`. The archived source reproduces that
error at line 177, followed by elaboration errors in the dependent declarations.

Specify `SheafOfModules.{u}`, as already required by `schemeDerivedCategory`,
`schemeDerivedBaseChangeMap`, `relativeMVAdj`, and `relativeMVComp`. This restores
the intended hypothesis rather than changing the mathematical statement. The
generic mate proof, pullback-coherence proof, public theorem text, public import,
and all definitions are preserved. No source-library module is edited.
No definition used by a target is changed; no target meaning review is reopened.

## Old

```lean
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules (moduleRings Z.toRingedSpace))]
```

## New

```lean
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeHorizontalMate | H2 | Restored archive; one universe annotation repaired; clean single-file compile. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeSourceTransport | no local claim; quarantined | The sole direct importer of this Sheaf module; its archived source compiles unchanged against the repair (25.7 s). Not included in the delivery. |
| WeilConjectures.AlgebraicGeometry.DerivedBaseChangeHorizontal | no local claim | DAG parent; its Lean imports the upstream mate twin, so it requires no adaptation. |

`tools/downstream.py` initially reports the assigned module unknown because it is
quarantined; its `--allow-missing` query is supplemented by direct import and
declaration-use searches through both `lean/` roots and `quarantine/Sheaf/`.
Those searches find only `DerivedBaseChangeSourceTransport` importing the assigned
Sheaf module. The other rows in `coord/rework.tsv` describe transitive quarantine
dependents, not additional current direct importers. The two DAG parents retain
their dependencies on `new-lem-pc-derived-base-change-horizontal-mate`.
The unit's realized route is unchanged. The original module archive is preserved.

## Status

landed 20261020T145516-L-2404822 2026-10-20 (merge of deliver/H2/Sheaf.AlgebraicGeometry.DerivedBaseChangeHorizontalMate)
