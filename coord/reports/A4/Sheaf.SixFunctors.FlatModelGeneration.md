## What changed

Restored the complete assigned rework module
`Sheaf.SixFunctors.FlatModelGeneration` from the exact quarantine path recorded in
`coord/rework.tsv`. Preserved all declarations, all three already proved etale clauses,
all imports and every dependency. Replaced six occurrences of the retired
`LocallyClosedStratification` type with the current upstream `Scheme.Stratification`:
the ordered predicate, its private filtration helper, the two ordered-stratification
theorems and the two filtration theorems.

On the Noetherian schemes in the item, locally closed strata are automatically
constructible. The migration therefore preserves the mathematical statement, arbitrary
scheme structures on the strata, coefficient universes, and the zero-strata empty case.
The definitions still have explicit data and contain no sorry. No source-library file
or target statement was changed. The DAG attachment and all proof dependencies remain;
only the recorded Lean statement and restoration note are updated.

Validation: the unmodified archive failed on the retired identifier. The migrated
complete module compiles through lcompile.py with exit code 0 in 38.2 seconds. Search
found no whole-item replacement; Loogle confirmed the existing Mathlib finite-presentation
flat-to-projective lemma used by the retained etale proof. Existing public signatures
were compared against the archive: only the stated type-name migration differs.
Archived consumers were reviewed for uses; no consumer adaptation is necessary.
The change record is `coord/changes/A4-restore-flat-model-generation.md`.

## Proved and sorry left

This delivery repairs the listed missing-module/API defect. It closes 0 of the 3
remaining archived holes, adds 0 holes relative to the archive, and splits off 0.
Restoring the absent module restores its 3 pre-existing holes to the active source;
this is not claimed as proof progress. The three etale clauses were already proved
in the archive and their proofs are preserved verbatim, not claimed as new work.

Every remaining sorry belongs to `det-sf-flat-model-generation` and keeps its full
source and natural-language proof docstring:

- `AlgebraicGeometry.proEtale_flatConstructible_orderedStratification`
- `AlgebraicGeometry.proEtale_flatConstructible_extensionFiltration`
- `AlgebraicGeometry.proEtale_flatConstructible_thickGeneration`

## No longer needed

None. No imports, declarations, modules, nodes or proof dependencies were removed.
The quarantine archive is preserved. In particular the unfinished pro-etale proof
route and its dependencies are not treated as withdrawn.

## Where the brief, the DAG or earlier work was wrong

The active module was absent after cluster restoration, but the archive and its Lean
attachment were still authoritative. Its remaining `LocallyClosedStratification`
references predated the documented upstream migration. Using `Scheme.Stratification`
repairs these references and lets the existing etale proofs compile unchanged.
The unit record still points at an older snapshot; this delivery does not alter
that maintainer-owned unit metadata or bypass its argument.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
