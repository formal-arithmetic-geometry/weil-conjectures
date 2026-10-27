# Sheaf.Paper.FieldOrientationSystemComparison instance repair

## Reason

Restore the quarantined module assigned by `coord/rework.tsv`. The archived
module fails because `WeilConjectures.scalarReductionSiteSmall` is not a registered
global instance. Its defining module now registers it only locally. Removing an
absent registration is an error in Lean, so the obsolete removal must be deleted.

## Old

The module is absent from `lean/`. The preserved quarantine version contains:

```lean
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
```

## New

Restore the complete quarantine version at
`lean/Sheaf/Paper/FieldOrientationSystemComparison.lean`, omitting that one command.
All declaration signatures, definitions, imports, and the other attribute commands
remain verbatim. The already absent global instance stays absent.

The proof also needs less elaboration to satisfy the per-file compile limit. In
`evaluation_single_shift_naturality`, specialize a proved private generic
exact-functor naturality lemma using the same two standard comparison isomorphisms.
The new private comparison definition is an explicit composite of those isomorphisms,
and the rewrite runs with abstract categories and coefficients. In `field_orientation_system_comparison`, use the source-heart
presentation composed with `oF` as the target presentation and replace unrestricted
simplification with `Iso.inv_hom_id_assoc`. These changes are internal proof steps;
there is no shared definition or transparency change.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FieldOrientationSystemComparison | H1 | Restored; obsolete command removed. |

Exact import search in `lean/Sheaf` and `quarantine` finds no direct Lean importers.
The DAG node `lem-sp-field-orientation-system-comparison` keeps its existing Lean
attachment, proof and dependencies. No target statement or definition changes.

## Status

landed 20261027T012841-L-2339271 2026-10-27 (merge of deliver/H1/Sheaf.Paper.FieldOrientationSystemComparison)
