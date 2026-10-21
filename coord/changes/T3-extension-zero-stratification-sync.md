# AlgebraicGeometry.Scheme.cbc_extension_zero_stratified_perfect

## Reason

Restore the quarantined module assigned in coord/rework.tsv. The upstream sync
removed the old LocallyClosedStratification interface. The archived private helper
still names it, while the existing IsIntegralStratifiedPerfect predicate now uses
AlgebraicGeometry.Scheme.Stratification. Adapt the helper to that current interface.
The archived construction already supplies every field of the current structure,
including constructibility of strata from Noetherianity. Its proof is retained.

## Old

In the archived private definition extendStratification:

```lean
    (s : LocallyClosedStratification U) : LocallyClosedStratification T where
```

## New

In the restored private definition extendStratification:

```lean
    (s : Stratification U) : Stratification T where
```

The complete public theorem signature, all public imports, every definition body
apart from these private type annotations, and every proof are preserved verbatim
from quarantine/Sheaf/Paper/ExtensionZeroStratifiedPerfect.lean. No source-library
module, target statement, instance registration, or elaboration option changes.
The node attachment and proof dependencies are preserved.

## Users

Source searches of lean/ and quarantine/ find no external occurrence of the theorem
name. The sole direct importer is the quarantined module below; its unfinished
proof still needs this dependency, which is restored rather than withdrawn.
No consumer adaptation is necessary: the changed helper is private and the public
statement remains exactly the archived statement, using the existing canonical
IsIntegralStratifiedPerfect predicate. Target meanings do not change.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | T3 | Restored; private helper uses the current stratification type. |
| Sheaf.Paper.IntegralCompactSupportUniformRestriction | unclaimed, quarantined | Same public theorem and imports; no adaptation. |

## Status

landed 20261021T120546-L-3910901 2026-10-21 (merge of deliver/T3/Sheaf.Paper.ExtensionZeroStratifiedPerfect)
