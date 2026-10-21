# AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_isLeftAdjoint_localizingLowerStar

## Reason

Restore the item from its preserved quarantine source, as assigned by row 77 of
`coord/rework.tsv`. The library file is absent after the cluster restore. Its archived
proof already compiles against the restored current proper-pushforward and cohomological
Brown interfaces. This is restoration of missing Lean declarations, not a new definition
or a change of their mathematical statements.

## Old

The library path `lean/Sheaf/AlgebraicGeometry/EllAdicLocalizingBrownRepresentability.lean`
is absent. The preserved source at the corresponding `quarantine/Sheaf/` path declares,
with the coefficient, scheme, and properness binders retained verbatim:

```lean
theorem ellAdic_localizing_lowerStar_hom_isRepresentable
    (K : (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory) :
    ((ellAdicLocalizingLowerStar Λ ℓ g hΛ).op ⋙ yoneda.obj K).IsRepresentable

theorem ellAdic_isLeftAdjoint_localizingLowerStar :
    (ellAdicLocalizingLowerStar Λ ℓ g hΛ).IsLeftAdjoint
```

## New

Restore the entire archived module verbatim to its library path, including both complete
proofs and all public and private imports. Both declaration signatures above and their
section binders are identical. No definition, instance, target, or source-library file changes.
The quarantine archive remains untouched.

## Users

`tools/downstream.py` reports the item as unknown because its library path is absent.
A source search of both `lean/` and `quarantine/` finds these two direct consumers.
Neither is adapted by this delivery; restoring the exact interface preserves their meanings.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | no matching claim found | Quarantined consumer: its call to ellAdic_isLeftAdjoint_localizingLowerStar is restored unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | no matching claim found | Quarantined consumer: its call to ellAdic_isLeftAdjoint_localizingLowerStar is restored unchanged. |

## Status

landed 20261021T020119-L-2586292 2026-10-21 (merge of deliver/F4/Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability)
