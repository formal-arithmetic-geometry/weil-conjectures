# CategoryTheory.InternalAbelianSheafModule.internal_section_scalar_adjunction

## Reason

The completed proof adds private helpers, a namespace opening, declaration-scoped
`omit` commands, and proof imports. The interface scanner conservatively reports
these commands as an interface change, so this record documents them and their
consumers. Existing public declarations, definitions, public imports and the
exported additive-instance attribute remain unchanged. No target meaning changes.

## Old

```lean
attribute [instance] SheafOfModules.ScalarDerivedPair.extension_additive
```

```lean
theorem internal_section_scalar_adjunction : InternalSectionScalarAdjunction J a := by
  sorry
```

There was no `open SheafOfModules` command or helper-specific `omit` scope.

## New

```lean
attribute [instance] SheafOfModules.ScalarDerivedPair.extension_additive
```

```lean
theorem internal_section_scalar_adjunction : InternalSectionScalarAdjunction J a := by
```

The theorem now has a complete proof of the same proposition. The new
`open SheafOfModules` resolves helper names within this file. Each added `omit ... in`
command scopes only the next private helper and removes unnecessary section
instances from its type. These commands add no global instance or public notation.
The new public theorem `derived_section_scalar_transport` lives in its own
`Sheaf.CategoryTheory.DerivedSectionScalarTransport` module with its own node.

## Users

The direct and transitive Lean importers coincide. The source search and
`tools/downstream.py --uses internal_section_scalar_adjunction` were used to audit
consumers. The command changes and unchanged theorem signature require no consumer
adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.InternalSectionScalarAdjunction | A4 | Complete proof; existing public interface preserved. |
| Sheaf.Paper.IntegralGeneralLfpHomInversion | P2 | Unchanged; no adaptation needed. |
| Sheaf.Paper.LocalizedDirectImageComparison | S2 | Unchanged; no adaptation needed. |
| Sheaf.Paper.ProperIntegralRationalScalarComparison | Q9 | Unchanged; no adaptation needed. |

## Status

landed 20261021T161401-L-4160359 2026-10-21 (merge of deliver/A4/Sheaf.CategoryTheory.InternalSectionScalarAdjunction)
