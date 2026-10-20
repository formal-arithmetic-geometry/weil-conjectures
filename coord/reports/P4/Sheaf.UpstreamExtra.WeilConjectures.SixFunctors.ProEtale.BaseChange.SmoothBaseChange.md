## What changed

Restored the assigned quarantined module, retaining its proved private
`comparison_mate_transport` lemma and all original public imports. Removed the
orphaned `variable (p) in` left by extraction and disabled the private-only-module
linter for this compatibility file. Rewrapped the extraction comment.

Repaired the unclaimed dependency
`Sheaf.SixFunctors.ProEtale.BaseChange.SmoothBaseChangeComparisons`: it now publicly
imports the upstream smooth base-change module instead of redeclaring its five
comparison constructions. All five declaration texts were checked byte-for-byte
against upstream and are identical. Updated only the definition node's Lean
attachment to the upstream module, preserving all five names and dependencies.

Change record: `coord/changes/P4-smooth-base-change-comparison-sync-repair.md`.

## Proved and sorry left

This is a zero-hole sync repair: 0 holes closed, 0 holes added, 0 holes left in
either delivered module, and 0 split off. The private `comparison_mate_transport`
proof is retained unchanged. The upstream theorem `comparison_derivedBaseChangeMap`
still has its pre-existing sorry; it is outside this assigned repair and is neither
changed nor counted as closed. No public mathematical statement is changed.

The original archived file failed with the reported duplicate-definition import
error. After that repair, compilation exposed and confirmed the dangling-scope
error. Both delivered modules and all nine live downstream modules compiled cleanly
through `lcompile.py --all`, individually in 0.6–9.7 seconds. Consumers checked:
`TorsionStalkProEtaleResolutionMap`, `ComparisonCounit`, `ComparisonSquarePaths`,
`ComparisonSquareEtalePathNormalization`, `ComparisonSquareProEtalePathNormalization`,
`ComparisonSquareTransport`, `ComparisonSquare`, `CompactSupportProperFactor`, and
`CompactSupportSiteComparisonOpen`. Consumer copies were unchanged and are not
part of the delivery. The additional quarantined direct consumer
`Sheaf.Paper.ProperDirectImageFiniteness` also compiled unchanged in 12.3 seconds.

## No longer needed

Removed the duplicate local definitions of
`rightDerivedLowerStarComparisonPlusIso`, `rightDerivedLowerStarComparisonIso'`,
`leftDerivedUpperStarComparisonIso`, `baseChangeSourceComparisonIso`, and
`baseChangeTargetComparisonIso` from the comparison compatibility module. These
same fully qualified declarations remain available from upstream with identical
signatures and bodies.

The compatibility module's four direct upstream imports are replaced by its one
public import of the upstream smooth base-change module, which publicly imports
all four. No mathematical dependency, node, or module is pruned. The assigned
module retains its ComparisonCounit and ComparisonSquare imports. In particular,
the canonical counit and square obligations in the transport node remain needed.

## Where the brief, the DAG or earlier work was wrong

The assigned item has no sorry and no current DAG Lean attachment: it is a
quarantined extraction repair. Its imports mixed the restored upstream canonical
comparison definitions with a Sheaf extraction that defined the same names again.
The extraction also left `variable (p) in` with no declaration after it. The related
definition node still pointed to the duplicate Sheaf definitions. The repair
restores the archive, reconciles the duplicate definitions with upstream, and
preserves the node's meaning and dependencies. No upstream file is edited.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
