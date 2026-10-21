# IntegralCanonicalTruncations local instance priorities

## Reason

The new proofs quantify over arbitrary sheaves of coefficient rings on a pro-etale
site. Prefer the existing general standard derived-category instances over the
specialized coefficient instances while elaborating this file. These are `local`
attribute commands and change no imported instance registry, public declaration
signature, object, morphism, or definition. The delivery checker conservatively
classifies the added attribute commands as an interface change and requires this
record. No mathematical interface repair or downstream adaptation is needed.

## Old

```lean
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
```

## New

```lean
set_option synthInstance.maxSize 2048
universe u

attribute [local instance 2000] AlgebraicGeometry.Scheme.reductionRingModulesHasDerivedCategory
attribute [local instance 2000] AlgebraicGeometry.Scheme.pbcTowers_hasDerivedCategory
open CategoryTheory CategoryTheory.Limits Opposite
```

The additional elaborator transparency settings are proof options. All twelve
pre-existing public declaration signatures and all public definition bodies remain
verbatim. Public imports retain the same modules; added imports are private.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralCanonicalTruncations | C1 | Local elaboration priorities for the new private helpers and theorem proofs; no public signature changes. |
| Sheaf.Paper.IntegralTStructure | unclaimed; quarantined restoration item | Its archived source publicly imports this item. No adaptation: local attributes are not exported and every pre-existing declaration remains available unchanged. |

A source search found no live Lean importer of the quarantined item; the archived
IntegralTStructure is the direct quarantined importer. No changed declaration name
exists for downstream `--uses` filtering: this record covers local commands only.
The DAG parents and their dependencies are preserved except for the parent proof
route update, which is included in this packet. No source-library file is changed.

## Status

landed 20261021T020101-L-2583698 2026-10-21 (merge of deliver/C1/Sheaf.Paper.IntegralCanonicalTruncations)
