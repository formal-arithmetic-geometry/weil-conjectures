## What changed

Restore `lean/Sheaf/Algebra/Homology/FilteredTensorLocalization.lean` from the exact
archive named by its current `coord/rework.tsv` row. The assigned repair is the
missing quarantined module, reverted after a cluster restore. This delivery restores
all eleven declarations, including the representative maps, canonical comparison
composites, and the original localization theorem. The archive, its DAG attachment,
and its dependencies are preserved. No definition, statement, proof route, or public
import is changed relative to the archive.

The canonical-import dependency repairs have already landed: H2 repaired
`FiniteFilteredModuleHomotopy`, and M2 repaired `FilteredTensorGradedComparison` and
restored `FiniteFilteredKFlatReplacement`. With those exact current dependency sources,
the restored item compiles cleanly (20.7 seconds). The sandbox includes unchanged copies
of these three current dependency modules solely to compile against their repaired
sources while the published server build still has missing/stale artifacts. They do
not change in this delivery.

The two direct archived consumers are
`Sheaf.Algebra.Homology.DerivedCanonicalFiltration` and
`Sheaf.Algebra.Homology.BoundedTensorTorSpectralSequence`. Their imported names and the
full localization theorem signature are restored verbatim. They keep their separate
quarantine/rework assignments; this delivery does not withdraw or adapt them. The queue
records sixteen quarantined transitive importers waiting for this restoration.

## Proved and sorry left

This is a quarantine restoration, not a proof or a decomposition. Holes closed: zero.
Holes added relative to the quarantined item: zero. No statements are split off.

The one original hole remains:
`CochainComplex.filteredTensor_localization`, node
`lem-kun-filtered-tensor-localization`. Its complete nine-step proof plan and source
remain in its docstring and existing DAG node. The ten existing definitions are restored
verbatim, with no holes in their bodies. In particular the graded-comparison extraction
is still the dependency's canonically characterized comparison, not a new arbitrary
existence choice.

The unchanged dependency copies retain their existing holes in
`CochainComplex.filteredTensor_graded_comparison` and
`CochainComplex.finiteFiltered_kFlat_replacement`; neither is added or altered here.
`FiniteFilteredModuleHomotopy` has zero holes.

## No longer needed

None. No import, declaration, node, module, or dependency is pruned. The unit's route
and the item's `stmt_deps`, `proof_deps`, proof steps, and Lean attachment are unchanged.

## Where the brief, the DAG or earlier work was wrong

The item is absent from the active `lean/` tree, but it is not withdrawn: the rework row
points to its intact quarantine source. The initial single-file compile failed because
the published build lacked `FiniteFilteredKFlatReplacement.olean`. A diagnostic compile
of the current replacement source against published artifacts also encountered the old
Sheaf finite-filtration import collision. Compiling the current, already repaired
`FilteredTensorGradedComparison`, `FiniteFilteredModuleHomotopy`, and
`FiniteFilteredKFlatReplacement` sources in dependency order resolved both artifact
problems, and the archived item then compiled without any source repair. There is no
remaining item-level API mismatch to patch or statement to weaken.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
