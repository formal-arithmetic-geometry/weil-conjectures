# KInjectiveWords proof-local attributes

## Reason

The eleven theorem proofs need the existing preservation theorem as a local instance and
use the right-derived-functor APIs without unfolding their large constructions. Preflight
classifies added attribute commands conservatively as changes to what other modules see.
Both commands explicitly have local scope. All 29 existing declaration signatures and all
public definitions and imports are unchanged. No target meaning changes, and no consumer
adaptation is necessary.

## Old

There were no local attribute commands for these declarations in the module.

## New

```lean
attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
attribute [local instance] Word.preservesKInjectives
```

The first command is before the namespace; the second follows the proved preservation
theorem. They control elaboration only in this module. Private proof imports and proved
private helpers support the completed proofs. No public instance attribute is added.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.KInjectiveDirectImageOpenWordModel --uses
AlgebraicGeometry.ProEtale.KInjectiveWords.Word.preservesKInjectives` reports the single
transitive importer below and only the item itself as a textual declaration user. Reading
the importer confirms that its import is private and it does not mention KInjectiveWords.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.KInjectiveDirectImageOpenWordModel | X5 | Local proof elaboration; eleven holes filled; signatures preserved. |
| Sheaf.Paper.TransverseTameOpenShriekExchange | unclaimed | Existing signatures and definitions unchanged; local attributes do not export; no adaptation. |

## Status

landed 20261021T174254-L-3776776 2026-10-21 (merge of deliver/X5/Sheaf.AlgebraicGeometry.KInjectiveDirectImageOpenWordModel)
