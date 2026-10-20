# AlgebraicGeometry.comparison_fst

## Reason

Restore the zero-hole quarantined module
`Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent`.
For the return of `7d5eaf21a2` (base `6488bba00`), reread the current shared
source and regenerate the repair from the current quarantined version. The item
is absent from `lean/` and assigned for restoration in `coord/rework.tsv`; U5 still
holds the claim. The current archived helper signatures and complete proofs agree
with the retained returned packet. No newer helper edit is overwritten. The
delivery tool constructs the replacement commit on its current `sheaf-dag` base.
Its trailing scoped linter option has no following declaration and instead applies
to the namespace closing command, causing the recorded parser error. The first
dry run requests this record for the module-level command change.
Both private helper signatures and proof bodies stay verbatim. Every public import
stays verbatim. No target statement or definition changes.

## Old

The original trailing commands, verbatim:

```lean
set_option linter.unusedVariables false in
end AlgebraicGeometry
```

The original option before the helpers, verbatim:

```lean
set_option autoImplicit false
```

## New

The corrected trailing command:

```lean
end AlgebraicGeometry
```

Options before the helpers:

```lean
-- Both retained comparison lemmas are private proof helpers.
set_option linter.privateModule false
set_option autoImplicit false
```

The private-module linter is disabled for this helper-only extracted module so
single-file compilation is warning-free. The generated provenance comment is also
wrapped to 100 columns, without changing its content.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent | U5 | Restored from quarantine; scope closure repaired; both helper proofs preserved. |

No live Lean module imports this quarantined module. No consumer adaptation is
needed, and there is no DAG attachment to change for these private helpers.

## Status

landed 20261020T150711-L-2575700 2026-10-20 (merge of deliver/U5/Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent)
