# AlgebraicGeometry.affineSections_square_mate_path_unit

## Reason

The main theorem's specialization repeatedly expands localization constructions.
The delivery keeps the construction interfaces locally irreducible while specializing
and disables the optional let-to-have cleanup transformation for this declaration.
The static checker classifies the added local attribute commands and the relocation
of the unchanged section variables as an interface change, so this record documents them.
These are local elaboration settings: no signature, definition body, instance or
exported attribute changes. The theorem's original signature and docstring are
byte-for-byte unchanged. Full kernel checking remains enabled.

## Old

The original file has no local irreducibility attributes or cleanup option.
Its section variables are:

```lean
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]
```

The theorem was `:= by sorry`. The same signature is retained in the delivery.

## New

The same section variables now follow the proved generic private helpers, so those
helpers do not acquire irrelevant section assumptions. Before the public theorem:

```lean
attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  Functor.mapDerivedCategory Functor.rightDerivedFunctorCompUnit
  Functor.rightDerivedFunctorCompMapDerivedCategoryIso
  canonicalPullbackAdjunction affineGlobalSectionsDerivedIso
```

The declaration is scoped under these options:

```lean
set_option linter.all false in
set_option cleanup.letToHave false in
set_option maxHeartbeats 800000 in
```

The lint option avoids expensive linting of the retained nondependent forall binders;
none of these options disables kernel checking or raises the file's time limit.
The construction definitions themselves are unchanged. The new proof-only import
and the new sheaf-level intermediate theorem are described in the item report.

## Users

The declaration-use query reports the following modules. The module has one direct
importer, AffineSectionsSquareComparisonCoherence; its 342 transitive importers see
exactly the original theorem type. Local attributes end with this module and scoped
options end with the declaration, so no consumer needs adaptation and no target
statement or definition is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineSectionsSquareMatePathUnit | T2 | Proof and local elaboration settings only; same public signature. |
| Sheaf.AlgebraicGeometry.AffineSectionsSquareComparisonCoherence | unclaimed | Same theorem signature and exported attributes; no adaptation. |

## Status

landed 20261013T151136-L-878245 2026-10-13 (merge of deliver/T2/Sheaf.AlgebraicGeometry.AffineSectionsSquareMatePathUnit)
