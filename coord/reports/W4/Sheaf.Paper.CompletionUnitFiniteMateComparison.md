## What changed

Restored lean/Sheaf/Paper/CompletionUnitFiniteMateComparison.lean from the module
preserved at quarantine/Sheaf/Paper/CompletionUnitFiniteMateComparison.lean,
incorporating the retained W4 performance improvement and fixing the actual
compiler failure recorded in coord/build-errors for this module.

The returned head 1e505714e03 was based on c804a0ae5. In the meantime the red-build
quarantine commit 53d492a359f removed the module and its importer closure from
lean/. The current coord/rework.tsv row identifies the archived source and the
failure after J6's coefficient calculus change. W4's existing claim is retained.
This delivery restores that rework item; it neither withdraws the module nor
changes or deletes the quarantine archive.

The finiteModel_unit helper now explicitly closes the residual goal
(asIso f).hom = f by reflexivity after rewriting the mapped identity and
categorical identity factors. The earlier delivery omitted this final equality,
which is needed after the coefficientLocalizedCounitModel wrapper was introduced.
The archive already includes this final rfl, and this restoration preserves it.
Thus this repair changes the previously returned proof and is not a rebase or
unchanged re-push.

The private square_factors helper still performs localization-factor cancellation
in the generic abelian-category setting. system_projection applies its normalized
identity directly, retaining the performance improvement of the returned head.
The restored module compiled through lcompile.py in 44.4 seconds, exit code 0,
without warnings. The delivery command runs its own compile and dry-run preflight
before pushing. The public finiteComparison_of_unit theorem signature agrees verbatim with the
quarantine source. All declarations, public imports and dependencies are retained;
no consumer interface changes. The item's DAG proof and proof_origin describe
these two private proof adjustments; its Lean attachment is preserved.

## Proved and sorry left

Holes closed: 0. Holes added: 0. Holes remaining in the restored module: 0.
WeilConjectures.CompletionUnit.finiteComparison_of_unit and all six private helpers
remain completely proved. The associated node is
lem-trf-completion-unit-finite-mate-comparison. No statements were split off.
This is a compiler compatibility repair and restoration, with the previous
performance repair retained, not a claim of new hole reduction.

## No longer needed

No imports, nodes, declarations, modules or mathematical dependencies are pruned.
The specialized cancellation and simplifier transport inside system_projection
remain replaced by direct application of the generic square_factors helper.
The blueprint unit route and all declared dependencies are preserved.

## Where the brief, the DAG or earlier work was wrong

The return is addressed by restoring the current quarantined module as its rework
item, preserving the original statement and Lean attachment, and repairing the
actual finiteModel_unit compiler failure reported with the quarantine row.
The earlier sandbox compiled against the previously published calculus but did not
include the residual asIso_hom equality required by the updated construction.
The repair explicitly supplies that equality. No mathematical statement error or
reason to weaken the theorem was found. The archive and every importer outside
this item are untouched because the restored module's public interface is intact.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
