# Sheaf.UpstreamExtra.WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing

## Reason

Restore the zero-hole quarantined companion after synchronization left a scoped
attribute immediately before a section terminator. The scoped command consumes
`end LowerShriek` and Lean reports a scope-name mismatch. Preserve every helper
and import; repair only the invalid command. The private-module linter is disabled
because every retained declaration is explicitly private.

## Old

```lean
attribute [local instance] Compactification.over in
end LowerShriek
```

## New

```lean
end LowerShriek
```

After the public section marker, add:

```lean
-- The synchronization companion retains only private helpers.
set_option linter.privateModule false
```

The generated module comment is wrapped to the line-width convention.
Every declaration body and signature and every import is unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.UpstreamExtra.WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | V5 | Restored and repaired section parsing; zero holes. |

A search of all active and quarantined Lean modules found no imports of this
companion. It has no public declarations and no attached DAG nodes. The imported
upstream QuasiFiniteVanishing module remains unchanged. No targets change meaning
and no consumer adaptation is required.

Repair of return `d2842da8b` (base `aacbf8401`): the current active library path
is absent, while `coord/rework.tsv` continues to assign restoration from the
quarantine archive. Reconstructed the delivered file from that current archive,
reapplied the scoped-command repair, and checked the five private declarations
and imports against the returned version. They agree. No independently changed
declaration or import is overwritten. The archive is preserved; no withdrawal
or empty replacement is proposed.

## Status

landed 20261020T150712-L-2575990 2026-10-20 (merge of deliver/V5/Sheaf.UpstreamExtra.WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing)
