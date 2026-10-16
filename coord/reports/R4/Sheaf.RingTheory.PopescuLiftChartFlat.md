## What changed

Proved the target theorem by a real reduction to two named intermediate local statements. Added `Sheaf.RingTheory.PopescuLiftChartPartialFlat`, and proved its equation-count flatness argument from the fibre-dimension theorem. Added `Sheaf.RingTheory.PopescuLiftChartMapsFlat`, isolating the remaining annihilator and local comparison transport. The target derives the prime membership and chart coefficient condition using `polynomial_value`, then applies the two intermediate statements. Removed proof-only imports of the old comparison and annihilator modules from the target; those dependencies remain in the intermediate module where needed.

## Proved and sorry left

Closed the one original hole, `Algebra.popescu_lift_chart_flat`
(`lem-weil-pbc-popescu-lift-chart-flat`). Both new intermediate declarations,
`Algebra.PopescuLiftPresentation.partial_chart_flat_repair` and
`Algebra.PopescuLiftPresentation.chart_maps_flat_of_partial`, are proved as well.
Added zero holes and left zero holes. This is a proof, not a decomposition with
new obligations; all three declarations use only the standard three axioms.

## No longer needed

The target no longer directly imports
`WeilConjectures.RingTheory.AnnihilatorElementFlatBaseChange` or
`Sheaf.RingTheory.PopescuLiftChartComparison`; their uses are isolated in
`PopescuLiftChartMapsFlat`. In that new module, removed the unused import of
`PopescuLiftChartPartialFlat` and the redundant import of `Mathlib.RingTheory.RingHom.Flat`;
changed the comparison import to proof-only and exposed only `PopescuLiftPartialChart`.

All eight former direct target proof dependencies are now reached through the new
intermediates or used as definitions in signatures: `def-weil-pbc-flat-ring-map`,
`def-weil-pbc-localization-at-prime`, `lem-weil-pbc-annihilator-element-flat-base-change`,
`lem-weil-pbc-equation-count-fibre-dimension-flat`, `lem-weil-pbc-flat-over-localization`,
`lem-weil-pbc-popescu-lift-chart-relations`,
`lem-weil-pbc-popescu-lift-partial-chart-dimension`, and
`lem-weil-pbc-popescu-lift-preparation`. Replaced their direct edges by the two new
intermediate nodes. No existing node or module leaves the target import closure;
none is claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The partial-chart flatness theorem was commented out as an upstream-sync repair;
the delivered module restores that proof under a fresh name, using the existing
fibre-dimension theorem. Contrary to the first report's claim, the final local
comparison was already exposed as `chart_comparison_bijective`: the new maps
theorem uses it directly, together with annihilator base change and localization
of flatness. The original target node still described an older inline proof;
the second reading updated it to the actual two-intermediate route.

## New nodes

`lem-weil-pbc-popescu-lift-chart-partial-flat-repair` records the equation-count proof of the partial chart flatness. `lem-weil-pbc-popescu-lift-chart-maps-flat` records the annihilator and local comparison transport to the full chart. Both node files are in the sandbox DAG copy.

## Second reading by R4

1. **Signatures and unchanged statements.** Compared the delivered target with the
   repository version. The target theorem signature is byte-for-byte unchanged. The
   two added declarations are intermediate statements below the existing unit and do
   not alter any existing declaration.
2. **Proof and axioms.** Compiled all three delivered modules with `lcompile.py`.
   There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by` declarations. Axiom inspection gives only
   `propext`, `Classical.choice`, and `Quot.sound` for the target and both added
   declarations.
3. **Statements and new nodes.** Checked both added statements against their
   docstrings and the corresponding Lean declarations. The partial-chart statement
   is exactly the equation-count flatness subclaim; the maps statement is exactly the
   local comparison transport subclaim. Both are strictly smaller than the target,
   have Stacks Tag 07CP sources, and have matching DAG nodes. Read Tag 07CP's
   partial-chart equation count and final comparison paragraphs. The zero ring has
   no relevant prime; when pi is a unit the partial-flat hypotheses have no prime
   satisfying hpi. When pi is zero the annihilator equality and annihilator
   transport remain valid. Empty equation sets use `(n+0)-0=n`, and no cancellation
   of pi occurs. Searched the library by chart/localization terms and repeated
   LeanFinder/Loogle searches: generic flatness transport results are used, and no
   active duplicate of either added declaration was found. The old partial-flat
   declaration occurs only in a comment.
4. **Pruning and route.** The target now uses the two intermediate declarations,
   while the lower equation-count, annihilator, comparison, and localization lemmas
   remain available through their respective modules. The target's direct proof-only
   imports of the old comparison and annihilator modules are removed. The unit route
   `sk-thm-p1` is retained through the partial-chart and local-comparison nodes.
5. **DAG agreement.** Updated the target node's proof and `proof_deps` to name the
   two intermediate nodes and the declarations used by the target proof. The two new
   node files have complete source, proof, search, Lean, chapter, and unit metadata.

The second reading found no mathematical defect or changed existing signature.
I repaired the helper's public proof-only imports, removed two unused/redundant
imports, corrected the partial-flat blueprint id, added module source docstrings,
expanded the comparison proof explanation, updated the target and new-node metadata,
and corrected the report's hole counts and earlier comparison claim.
