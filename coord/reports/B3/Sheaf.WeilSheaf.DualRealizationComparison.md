## What changed

Restored `Sheaf.WeilSheaf.DualRealizationComparison` from the quarantine archive
specified in `coord/rework.tsv`. Repaired the deterministic heartbeat timeout in the
final composite identity of
`WeilConjectures.NativeDualRealization.dual_realization_comparison`: the concrete
calculation now applies a proved private categorical cancellation lemma rather than
running rewrite matching over the full realization construction.

Removed the two old `backward.isDefEq.respectTransparency` disabling options.
Every existing public signature, definition body, instance and public import is preserved.
The repaired module compiled through `lcompile.py` in 47.6 seconds with profiling;
profiling options were then removed for delivery. The delivery tool checks the final file.

Change record: `coord/changes/B3-dual-realization-cancellation-repair.md`.

## Proved and sorry left

This is a compilation repair of a zero-hole module: 0 of 0 sorries closed, 0 added,
0 split off, and 0 left in the restored item. The main theorem
`WeilConjectures.NativeDualRealization.dual_realization_comparison` retains its complete
assembly proof. The new private `cancel_comparison` is fully proved.

The existing imported obligations
`WeilConjectures.NativeDualPresentation.ordinary_closed_presentation`
(`lem-sf-ordinary-closed-presentation`) and
`WeilConjectures.NativeDualPresentation.structural_omega_hom_pairs`
(`lem-sf-structural-omega-hom-pairs`) remain dependencies; this delivery neither creates
nor modifies their holes. No definition contains a sorry.

## No longer needed

None. No imports, modules, nodes or proof dependencies are pruned. The native closed
forgetful comparison, ordinary closed presentation, structural omega permitted pairs,
exceptional comparison, and constructible realization are all used by the unchanged
mathematical argument. No new nodes are needed for elementary categorical cancellation.

## Where the brief, the DAG or earlier work was wrong

The item is an assigned quarantine repair, not an unproved theorem: its archive already
contains zero sorries. The precise recorded failure is archive line 634 in inverse
cancellation, after the naturality construction. Performing that cancellation abstractly
avoids the concrete rewrite elaboration timeout. The DAG's argument and Lean attachment
are preserved, as are the quarantined source and its dependencies. No mathematical
statement was disputed or changed. Exact direct-import searches over both live and
quarantined Lean sources found no importers requiring adaptation.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
