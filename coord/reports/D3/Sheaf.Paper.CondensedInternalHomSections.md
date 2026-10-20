## What changed

Restored `lean/Sheaf/Paper/CondensedInternalHomSections.lean` from its quarantine
archive and repaired its assigned post-sync compile error. The private helper
`CategoryTheory.Mod.relativeTensorRightIso` now lives in
`Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian`.
Added a proof-only `import all` of that module so the existing tensor-unit argument
can use it. Preserved all three public imports and the theorem statement, including
its universes and hypotheses. No other module, definition or statement changes.

The three-step DAG argument remains unchanged: terminal-object evaluation, the
free-module adjunction, and the tensor-Hom adjunction followed by the unit isomorphism.
No node update or change record is needed because this repairs only proof visibility.

Validation: the original archive fails at line 76 with unknown
`Mod.relativeTensorRightIso`; the repaired file compiles cleanly through `lcompile.py`
in under four seconds. An axiom probe for
`AlgebraicGeometry.ProEtale.condensed_internal_hom_sections` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`. The import-direction check passes.
All declarations and public imports retain their archived signatures and visibility;
consumers therefore require no adaptations.

## Proved and sorry left

This assigned restoration/compile repair starts with zero `sorry` holes and ends
with zero. Holes closed: none (0). Holes added: none (0). No split-off statements.
`AlgebraicGeometry.ProEtale.condensed_internal_hom_sections` is fully proved and
sorry-free, as are both private helpers `freeUnitRegularIso` and `regularSectionsIso`.
Its node remains `lem-weil-pbc-condensed-internal-hom-sections`.

## No longer needed

Removed the obsolete proof import
`import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian`:
its private tensor comparison moved to the `Sheaf.UpstreamExtra` module, imported
in its place. No mathematical dependency, node or module is pruned. Both stated
DAG dependencies remain needed; the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proving holes, but the current `coord/rework.tsv` row
assigns a zero-hole post-sync restoration. The archive's `import all` still targeted
the upstream module after the private helper moved to `Sheaf.UpstreamExtra`.
The existing public import of the latter cannot expose its private helper, so a
separate proof-only `import all` is required. No mathematical error was found in
the statement or the DAG proof.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
