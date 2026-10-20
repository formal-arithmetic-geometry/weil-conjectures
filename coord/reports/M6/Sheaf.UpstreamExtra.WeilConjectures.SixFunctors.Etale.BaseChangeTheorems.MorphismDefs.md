## What changed

Reapplied the syntax repair to the current quarantined copy of
`Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`,
following the return of delivery 7d126929b7 (base 6488bba00). The current live path is absent;
its current source is at the matching `quarantine/Sheaf/UpstreamExtra/` path recorded in
`coord/rework.tsv`.

Removed the empty `BaseChangeTransformation` section, including its unused variables and
orphaned `variable {f g f' g'} in` command. The migration moved all declarations from that
section upstream but left the declaration-scoping command immediately before its `end`.
Removing the entire empty section repairs the parse error without leaving an unused scope.
The retained repair was compared afresh with the current quarantine archive; the complete
diff consists of this empty-section removal and the migration-comment wrapping below.
The migration comment is wrapped to 100 columns. Every public import, declaration signature,
and proof is preserved. The source-library file is unchanged.

The item and its unchanged quarantined consumer
`Sheaf.AlgebraicGeometry.DerivedSquareIsoCommShift` are compiled together in import order
against the repaired sandbox module. Both compiled without warnings. The equation lemma uses only
`propext`, `Classical.choice`, and `Quot.sound`.

Change record: `coord/changes/M6-morphism-defs-orphaned-variable.md`.

## Proved and sorry left

This is the assigned syntax repair of a module with zero holes.
Holes closed: 0. Holes added: 0. Holes remaining: 0. Split off: 0.
`AlgebraicGeometry.Etale.pullbackSquareComparison_def` remains completely proved by unfolding
and reflexivity; its existing node is `def-weil-pbc-derived-square-iso`.

## No longer needed

None. No imports, declarations, nodes, or modules are pruned. The removed empty section and
its unused variables are syntactic scaffolding, not declarations or proof dependencies.
The public imports preserve the extension module's re-exported interface.

## Where the brief, the DAG or earlier work was wrong

The returned delivery 7d126929b7 did not land because the item changed after base 6488bba00.
This revision rereads and starts from the current quarantined source,
reapplies the actual syntax repair, and removes the whole empty section left by extraction.
The recorded original failure is `Unexpected name BaseChangeTransformation after end:
The current section is unnamed`. The orphaned declaration-scoping command explains it.
No node statement, proof route, unit route, definition, or consumer is changed.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
