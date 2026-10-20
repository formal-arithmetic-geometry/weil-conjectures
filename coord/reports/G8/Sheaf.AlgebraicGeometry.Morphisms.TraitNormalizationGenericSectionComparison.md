## What changed

Completed the retire assignment listed in `coord/retire-items.tsv` for
`Sheaf.AlgebraicGeometry.Morphisms.TraitNormalizationGenericSectionComparison`.
The baseline module already compiled and contained zero holes. It is withdrawn through
`deleted.txt` in favor of the proved stronger upstream declaration of the same name.

Migrated the sole direct importer,
`Sheaf.AlgebraicGeometry.Morphisms.TraitDivisorChartSectionGenericFactor`, by replacing
its private import and the comparison application. The upstream theorem gives `ε` and
`β`; the existing proof sets `b = Spec ε`, discards the extra ring-map equation, and
continues with the same projection calculation. A declaration-local unused-variable
linter option accommodates the hypotheses retained in its unchanged signature.

Updated the attachment of `lem-sbc-trait-normalization-generic-section-comparison` to
the existing upstream module and explained the specialization. Updated the parent
node's third proof step to match the new call. All dependency edges and unit steps stay.
No source-library file is modified.

Change record: `coord/changes/retire-trait-normalization-generic-section-comparison.md`.

## Proved and sorry left

This is a duplicate retirement with **0 of 0 holes closed, 0 holes added, 0 split off**.
No `sorry` remains in any delivered Lean file.

`AlgebraicGeometry.Scheme.GaloisCover.trait_normalization_generic_section_comparison`
is already proved upstream. Its stronger statement implies the complete original
Sheaf signature: specialize the upstream theorem for each domain and fraction field,
obtain `ε, β`, and return `Spec ε, β` with the same projection equation.
A sandbox-only Lean check compiles that exact original signature under a fresh name;
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for both
this specialization and the upstream theorem.

`AlgebraicGeometry.Scheme.GaloisCover.trait_divisor_chart_section_generic_factor`
retains its original statement and a complete proof using the upstream comparison.
Server single-file compiles in import order verified the migrated consumer (7.3 s),
`StalkNormalizationTraitSectionLocalizedRootChart` (10.4 s), and
`StalkNormalizationTraitSectionRootPresentation` (27.3 s). The next unchanged module,
`StalkNormalizationTraitSectionChartGenericFactor`, hit the 60-second limit both with
these sandbox artifacts and in a separate compile against the unmodified published
baseline. This is a pre-existing compile-time problem, not a new compiler error from
the migration. The remaining indirect consumers were not recompiled; their imported
signatures and public imports are unchanged. No global build was run.

## No longer needed

Pruned module:
`Sheaf.AlgebraicGeometry.Morphisms.TraitNormalizationGenericSectionComparison`.
Removed its private import from `TraitDivisorChartSectionGenericFactor` and replaced
it with the corresponding `WeilConjectures` import. Its duplicate local proof and all
imports disappear with the withdrawn module. The upstream theorem supplies the same
comparison; no other mathematical dependency is removed.

No DAG node is deleted or discarded: the sole DAG parent still cites
`lem-sbc-trait-normalization-generic-section-comparison`, now realized upstream. The
unit `sk-prop-input-spreading` and its trait normalization route are preserved.
A source and quarantined-source search found no other importers or DAG parents.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief describes proving holes, but the current assignment is the
zero-hole retirement explicitly recorded in `coord/retire-items.tsv`. The retirement
inventory classified this twin as DIFFERENT because upstream reduced the hypotheses
and additionally returns the extending ring map. This difference only requires the
small consumer adaptation above; it does not require another proof chain or new nodes.

No false statement or mathematical error was found. The original Sheaf statement is
verified as a consequence of the existing upstream theorem. The old node's attachment
to the duplicate was the only obsolete mathematical record.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
