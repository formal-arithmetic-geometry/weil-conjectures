# AlgebraicGeometry.ProEtale.CondensedRing.ellAdicLocalizingLowerStar

## Reason

Restore the source module named by the current `coord/rework.tsv` row after the
upstream-sync cluster quarantine. The library path is absent, while the complete,
zero-hole implementation remains at
`quarantine/Sheaf/AlgebraicGeometry/EllAdicProperLocalizingPushforward.lean`.
The restored file compiles against the current published build without changes.
This repairs the missing module and its five declarations; it does not change a
definition or claim to close a proof hole. The archive is retained.

## Old

The `lean/Sheaf/AlgebraicGeometry/EllAdicProperLocalizingPushforward.lean` library
path is absent. Its archived restricted-functor definition is verbatim:

```lean
noncomputable def ellAdicLocalizingLowerStar :
    (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory ⥤
      (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory :=
  (boundedConstructibleLocalizingClosure Λ Y.left).lift
    ((boundedConstructibleLocalizingClosure Λ Z.left).ι ⋙ R((g.left)_*⟦Λ⟧))
    (fun K ↦ ellAdic_localizing_rightDerivedLowerStar_obj Λ ℓ g hΛ K.obj K.property)
```

## New

Restore the entire archived module byte for byte at its original library path.
The restricted-functor definition is verbatim:

```lean
noncomputable def ellAdicLocalizingLowerStar :
    (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory ⥤
      (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory :=
  (boundedConstructibleLocalizingClosure Λ Y.left).lift
    ((boundedConstructibleLocalizingClosure Λ Z.left).ι ⋙ R((g.left)_*⟦Λ⟧))
    (fun K ↦ ellAdic_localizing_rightDerivedLowerStar_obj Λ ℓ g hΛ K.obj K.property)
```

All existing signatures, docstrings, visibility, imports, instances, and proofs
are retained, including the membership and coproduct-preservation theorems.
No target statement or definition meaning changes. The existing DAG attachment
and proof plan remain valid and are not edited.

## Users

`tools/downstream.py` cannot index an absent module without `--allow-missing`.
The active Lean tree has no direct importers. An explicit search of both `lean/`
and `quarantine/` identifies these four archived direct consumers:

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed in the local claim snapshot | Quarantined direct consumer; archived interface preserved verbatim. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed in the local claim snapshot | Quarantined direct consumer; archived interface preserved verbatim. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed in the local claim snapshot | Quarantined direct consumer; archived interface preserved verbatim. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed in the local claim snapshot | Quarantined direct consumer; archived interface preserved verbatim. |

No consumer is changed. Brown representability and exceptional constructible
cohomology compile unmodified against the restored item. The archived boundedness
consumer fails independently at lines 559, 566, 572 (`Mod.monoidalClosed` has too
many arguments) and 660 (unknown `CategoryTheory.IsCompactObject`). Consequently
the combined exceptional-constructibility consumer was not reached by that
ordered compilation. These separate quarantined modules retain their rework
assignments. No original consumer becomes ill-typed because of this restoration.

## Status

landed 20261021T014710-L-2445969 2026-10-21 (merge of deliver/J1/Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward)
