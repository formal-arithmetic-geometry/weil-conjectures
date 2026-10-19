# CommonStageCalculus unused-section-variable checking

## Reason

Completing proofs leaves some section assumptions unused in proof bodies. Preserve every
existing signature and suppress only the unused-section-variable linter in this module.
The preflight classifies the added set_option command as an interface change, requiring
this record. This option changes lint diagnostics, not definitions or theorem statements.

## Old

```lean
set_option autoImplicit false
```

## New

```lean
set_option autoImplicit false
set_option linter.unusedSectionVars false
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CommonStageCalculus | G6 | Disable unused-section-variable lint diagnostics. |

The downstream.py scan found 893 transitive importers. All have the same effect:
no adaptation, because no exported signature, definition, instance or notation changes.
The linter option is scoped to this file. No declaration changes its signature or visibility.
Importers receive the same definitions and instances, with completed proof terms.
No downstream adaptation is required; no target statement or definition is changed.

## Status

landed 20261019T005300-L-2747823 2026-10-19 (merge of deliver/G6/Sheaf.Paper.CommonStageCalculus)
