## What changed

Restored `lean/Sheaf/Algebra/Homology/SplitFlatFilteredSheafModels.lean` from its
quarantine archive, preserving every definition, signature and public import.
Proved `SheafOfModules.FilteredFlat.widenProperty` by retaining finiteness and the
cochain bound and using filtration antitonicity at the two new interval endpoints.
Updated the existing definition node's proof record with this elementary argument.

The published compile cache still loads the old `Sheaf.CategoryTheory.Filtration`
through the finite-filtration dependency. Compiling the current, unchanged
`Sheaf.CategoryTheory.FiniteFiltrationInduction` and
`Sheaf.Algebra.Homology.UniformFiniteFilteredLocalization` sources in the sandbox
before the restored module resolves the duplicate `IsExhaustive` import error.
Those two sandbox sources are identical to the live sources and introduce no
repository changes. No definition or statement changed; no change record is needed.

Validation: all three modules compile in dependency order without warnings. The
quarantined direct consumer `Sheaf.Algebra.Homology.FiniteFilteredFlatSheafResolution`
also compiles unchanged against the restored module; its test copy is excluded from
this delivery. The interval proof allows equal endpoints and empty intervals: it
uses only the given endpoint equations, with no added nonemptiness assumption.

## Proved and sorry left

Closed the one archived hole:
`SheafOfModules.FilteredFlat.widenProperty`
(node `def-trf-split-flat-filtered-sheaf-models`).
One of one holes proved; zero holes added; zero holes remain in the restored module.
All original data constructions are retained. Nothing was split off.
The unchanged consumer's existing `finite_filtered_flat_resolution` hole is not
part of this delivery.

## No longer needed

None. All existing public imports, declarations, node attachments and dependencies
are preserved. The unit route and the quarantined parent's dependency are retained.
No modules are withdrawn. The interval proof requires no extra imports or nodes.

## Where the brief, the DAG or earlier work was wrong

The item is absent from `lean/` because it was quarantined, not withdrawn. Its
archive was restored without deleting or replacing the archived mathematics.
The recorded import collision is reproduced against the published compile cache;
the live finite-filtration sources already use the canonical upstream filtration
API. Recompiling those unchanged dependencies resolves it, and the existing
interval-widening hole is now fully proved. No mathematical statement was disputed.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
