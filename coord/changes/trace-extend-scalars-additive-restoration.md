# DerivedCategory.traceExtendScalarsAdditive

## Reason

Restore the quarantined TraceFormalLaws module. Its recorded sync failure is
`Unknown constant ModuleCat.extendScalars_additive_sheaf` at the instance body.
The existing scalar-extension adjunction proves the same additivity proposition.
This changes only a proof of a Prop-valued typeclass; statements, definitions of
trace, attributes, and public imports remain identical to the archived source.

## Old

```lean
noncomputable instance traceExtendScalarsAdditive {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) : (ModuleCat.extendScalars.{u, u, u} ρ).Additive :=
  ModuleCat.extendScalars_additive_sheaf ρ
```

## New

```lean
noncomputable instance traceExtendScalarsAdditive {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) : (ModuleCat.extendScalars.{u, u, u} ρ).Additive :=
  (ModuleCat.extendRestrictScalarsAdj ρ).left_adjoint_additive
```

## Users

The live-source downstream tool reports `unknown module` because the item is
quarantined. Searching both library roots and both quarantine roots finds these
three archived direct importers and no explicit use of the instance name. All
three remain quarantined and have no claim lock at this inspection. Their
signatures and meaning are preserved: this is a proof-irrelevant replacement,
and the exported instance has exactly its original type and name. No consumer
adaptation is necessary or included.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.DerivedCategory.TraceFormalLaws | W3 | Restore; replace broken proof. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Archived public importer; same interface. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | unclaimed | Archived proof importer; same interface. |
| Sheaf.Paper.CondensedPointSupertrace | unclaimed | Archived proof importer; same interface. |

No target statement or definition used by a target changes its meaning.

## Status

landed 20261020T174920-L-821091 2026-10-20 (merge of deliver/W3/Sheaf.CategoryTheory.DerivedCategory.TraceFormalLaws)
