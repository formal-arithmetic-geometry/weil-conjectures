# AlgebraicGeometry.Scheme.adicPerfectQuotientSectionAdjunction

## Reason

Document the additional local irreducibility attributes flagged by the static
preflight. They keep kernel checking of the existential assembly below the
60-second file limit. These attributes apply only while compiling this module;
they change no exported attribute, signature, definition, instance or public import.
The theorem's signature is literally unchanged. The added comparison import is
private. The new helper modules have their own DAG attachments.

## Old

```lean
attribute [local irreducible] derivedExtension extend change
```

## New

```lean
attribute [local irreducible] derivedExtension extend change
  adicPerfectQuotientFunctor adicPerfectQuotientModuleStep
  AdicQuotientSections.rightAdjoint AdicQuotientSections.adjunction
  AdicQuotientSections.step
```

## Users

Textual declaration-use search and the direct-import search find one consumer,
Sheaf.Paper.AdicPerfectUnitHom. Its source continues to obtain the same six
existential components from the unchanged theorem. No consumer adaptation is
needed: all new attributes are local to the item, and the proof dependency import
is private. The consumer is unclaimed in the current local claim records.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicPerfectQuotientSectionAdjunction | R2 | Local proof elaboration only. |
| Sheaf.Paper.AdicPerfectUnitHom | unclaimed | Same theorem signature and exports. |

The item and all four new helper modules passed compilation and axiom checks in
the delivery attempt. That attempt rejected only a new node's signature metadata:
lean.statement now records `structure SectionModel`, stopping before `where` as
required by the signature extractor. The mathematical node statement still
specifies every field of the structure.

## Status

landed 20261026T130650-L-3489467 2026-10-26 (merge of deliver/R2/Sheaf.Paper.AdicPerfectQuotientSectionAdjunction)
