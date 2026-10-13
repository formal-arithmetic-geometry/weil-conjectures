# AlgebraicGeometry.exists_mixedAffineSections_pullback_unit_normalization

## Reason

Preflight classifies proof-local commands as an interface edit. This record documents
only the local priority of the existing additive-functor zero-morphism instance and
the placement of section variables around private helpers. The public theorem signature,
visibility and public imports are identical to the original. No definition or target
statement changes, so no target meaning review is reopened. The priority avoids expensive
searches for zero-morphism preservation through homological-functor instances.

## Old

```lean
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]
```

No local instance priority registration or private helpers precede the public theorem.

## New

```lean
attribute [local instance 2000] Functor.preservesZeroMorphisms_of_additive
```

The same sheaf-derived variable precedes the private counit helper. The same module-derived
variable follows that helper, before the private sections-unit helper and the public theorem.
All newly added helpers are private and proved. These commands leave every existing public
signature unchanged; the original theorem signature was compared verbatim with the delivery.
The attribute is local to this namespace and does not export an instance change.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.MixedAffineSectionsPullbackUnitNormalization | V2 | Proof elaboration only; signature unchanged. |
| Sheaf.AlgebraicGeometry.MixedAffineSectionsChartModelFactorization | unclaimed in local claim snapshot | Sole direct importer and sole other textual user of the theorem; no public signature change, no adaptation needed. |

The private helper names have no downstream users. The exported theorem and definitions
have not changed, and all transitive importers therefore see the same statements.
No adapted module is included.

## Status

landed 20261013T171519-L-1983870 2026-10-13 (merge of deliver/V2/Sheaf.AlgebraicGeometry.MixedAffineSectionsPullbackUnitNormalization)
