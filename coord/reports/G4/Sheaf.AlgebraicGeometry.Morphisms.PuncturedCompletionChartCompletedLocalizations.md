## What changed

Proved `AlgebraicGeometry.Scheme.CompletionGluingData.exists_chart_completed_localizations`
with its signature and docstring unchanged. A fully proved private single-chart helper constructs
both maps jointly; the public proof chooses these pairs over the finite index family.
Added proof-only import `Mathlib.AlgebraicGeometry.Morphisms.Flat`.
The second reader removed the redundant explicit localized-module import; Flat supplies it transitively. Updated the existing node's proof and
proof_origin to the actual construction; proof_deps remain the same four definition nodes.

The section pushout yields the tensor comparison with both projection formulas. The overlap open
immersion identifies completed chart sections with overlap chart sections. Affine principal-open
localization gives the completed localization comparison; localization extensionality proves its
completed scalar compatibility. Composing these maps gives alpha and all four required equations.

Sources read: [Stacks 0BLH](https://stacks.math.columbia.edu/tag/0BLH), affine chart comparison,
and [Stacks 05EL](https://stacks.math.columbia.edu/tag/05EL), item (1). The missing local Stacks
checkout was supplemented by reading the official pages. Mathlib search used LeanFinder (affine
pullback tensor sections), Loogle (`IsLocalizedModule.linearEquiv_apply`), and grep. Existing
auxiliary tensor and localization proofs supplied useful implementations, but their existential
interfaces omit the generator equations; this proof constructs the maps with those equations.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Scheme.CompletionGluingData.exists_chart_completed_localizations`
(node `lem-sbc-punctured-completion-chart-completed-localizations`).
No sorry remains in this module. No holes or new nodes were added. This is a proof, not a
decomposition. The private single-chart helper is fully proved. Local compilation passed without warnings in 9.8 seconds. The delivery dry run passed its
compilation, axiom probe (only the three permitted axioms), and mechanical preflight; only the
second reading is pending, as required. Nothing was pushed.

## No longer needed

Removed the first draft's redundant proof-only import
`Mathlib.Algebra.Module.LocalizedModule.IsLocalization` after a successful deletion compile.
No repository imports were removed and no original proof_deps were pruned: the four definition
nodes remain necessary. The proof does not import or rely on
`PuncturedCompletionChartCompletedLocalizationsAlpha`, the retired
`PuncturedCompletionChartCompletedLocalizationsD`, `PuncturedCompletionChartTensorSections`,
`PuncturedCompletionChartTensorSectionsAux`, or `CompletedAffineSectionLocalization`.
These are alternative interfaces, not newly pruned modules from this item's original closure.
No claim is made that they are globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The existing change record `coord/changes/exists-chart-completed-localizations-d.md` correctly
identifies the arbitrary-alpha interface as false; this proof never chooses an unrelated alpha.
The tensor and completed localization existential interfaces do not specify generator values,
so they cannot alone justify the requested identities. Their constructions are reproduced with
the extra equations tracked explicitly, rather than deriving equations about arbitrary witnesses.
The original source route and unit remain unchanged. Empty principal opens and f=0 are handled
by Mathlib's localization and affine-section APIs without cancellation assumptions; t=0 is the
empty family choice.


## Second reading by G4

1. Compared the complete delivered module with the repository using diff and checked the
   existing theorem signature byte for byte by script. The public signature, visibility,
   docstring, definitions, and original public import are unchanged. Only a fully proved
   private helper, a proof-only import, and the replacement proof were added. No interface
   change record is needed.
2. Compiled the delivered file locally without errors or warnings (11.6 seconds). A scratch
   copy with `#print axioms` for
   `AlgebraicGeometry.Scheme.CompletionGluingData.exists_chart_completed_localizations`
   reports exactly `propext`, `Classical.choice`, and `Quot.sound`. Inspected the whole
   construction: the affine-section pushout fixes both tensor generator values; the overlap
   open immersion gives F; affine localization gives e with its generator value; localization
   extensionality proves C-scalar compatibility; alpha uses this same d. No sorry, custom axiom,
   unsafe mechanism, hollow definition, or arbitrary witness of an unproved existence theorem
   occurs. The chosen localized module action is determined on every fraction by its proved
   fraction formula. Verdict: a complete proof of the original statement.
3. No split-off statements, holes, or nodes were added. The private single-chart theorem is
   proved, and is the single-index construction used by finite choice. Checked f=0, f a unit,
   empty affine charts, and t=0: the argument uses localization universal properties and open
   restrictions without nonzero, cancellation, or nonemptiness assumptions.
4. Searched the library for completed localization and chart tensor comparisons, and read
   `CompletedAffineSectionLocalization`, `PuncturedCompletionChartTensorSectionsAux`, the
   section module definitions, and Mathlib's affine pushout-section theorem. The existing
   existential comparisons do not retain the generator equations needed here; no shorter
   applicable public interface was found. The direct proof avoids the retired false
   arbitrary-alpha interface. Tested each added import by compiling scratch copies: removing
   Flat loses the pushout-section theorem, while removing the explicit localized-module
   import compiles. Removed only that redundant import. No old proof dependency or repository
   import is pruned. Read the unit's realized record: this node is not a realized unit step,
   and the unit route is preserved.
5. Diffed the node record: only proof, proof_deps (unchanged), and proof_origin concern this
   delivery. All four old proof_deps remain used through the explicit section modules,
   matching data, formal-glueing operations, and adic completion. The four proof steps match
   the Lean construction and no node statement or Lean signature changed. Verdict: consistent.

Second-reading change: removed the redundant proof-only import
`Mathlib.Algebra.Module.LocalizedModule.IsLocalization` and updated this report. No proof or
statement repair was necessary. Holes closed: the one public theorem named above; holes added:
none. This is a proof, not a decomposition.
