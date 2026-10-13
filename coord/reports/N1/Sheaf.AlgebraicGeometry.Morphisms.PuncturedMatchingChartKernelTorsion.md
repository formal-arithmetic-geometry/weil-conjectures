## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.CompletionGluingData.puncturedMatching_chart_kernel_torsion`
by a localization reduction. Two proved private helpers identify the image of the double
open immersion as the principal open of `D.baseMap.hom f` and transport Mathlib's affine
principal-open localization instance to its section ring. The proof applies the geometric
numerator-vanishing substatement and `IsLocalization.exists_of_eq`, then extracts a power.
The original public signature, definitions and public import are unchanged.

Added `Sheaf.AlgebraicGeometry.Morphisms.PuncturedMatchingChartSectionInjective`, containing
`AlgebraicGeometry.Scheme.CompletionGluingData.puncturedMatching_chart_section_injective`.
Its public import supplies its signature; its plain proof import retains
`Sheaf.RingTheory.FormalGlueingH0Localization` and the original formal-gluing route.
The item imports the new module only for its proof. No change record is needed.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.CompletionGluingData.puncturedMatching_chart_kernel_torsion`
(node `lem-sbc-punctured-matching-chart-kernel-torsion`).

Hole added and left: `AlgebraicGeometry.Scheme.CompletionGluingData.puncturedMatching_chart_section_injective`
(node `lem-sbc-punctured-matching-chart-kernel-torsion-injectivity`), in the new module.
Its proof is exactly `by sorry`; its docstring supplies the source and complete
natural-language proof. There are no other new or remaining local holes.

This is a decomposition: one upper hole closed, one geometric comparison hole added,
net zero. It proves the affine image/localization and denominator-clearing parts of the
argument, while formalizing the geometric equalizer comparison remains open. Both public
declarations still use `sorryAx` through this one named hole; neither is an axiom-free result.

Both delivered modules compile without errors or warnings using `lcompile.py --all`.
Scratch-copy `#print axioms` checks of both public declarations show only `propext`,
`Classical.choice`, `Quot.sound` and `sorryAx`. Delivery validation also probes the helpers.

## No longer needed

No repository import or module is pruned. The original node dependency
`lem-weil-pbc-formal-glueing-H0-localization` moves below the geometric split node and
remains in the import closure; it is no longer a direct dependency of the item.
All other old dependencies remain. The draft's added import
`Mathlib.RingTheory.Localization.Away.Basic` was removed as unnecessary, with recompilation.
The chart power-lift declaration is not used directly by this kernel proof; it remains
an internal dependency of the formal H0 localization theorem.

## Where the brief, the DAG or earlier work was wrong

The original plan did not separately formalize the affine principal-open image and
localization transport needed to apply the zero criterion. The first draft's split
statement was placed in the item's module, had a mismatched blueprint tag, an incomplete
proof docstring and incomplete search records. Its report called the item proved without
identifying the one-for-one decomposition. These are repaired.

## New nodes

`lem-sbc-punctured-matching-chart-kernel-torsion-injectivity` records vanishing of a
matching numerator in the principal-open section ring, before denominator clearing.
It lives in the new module `PuncturedMatchingChartSectionInjective` with the same
chapter and unit as the item. Its proof follows Tags 0BLH and 05ER and the existing
formal H0 localization node. Searches with Lean Finder, Loogle, LeanSearch and grep
are recorded; LeanSearch returned an internal server error, not a negative verdict.
No definition or existing statement changed, so there are no change records.

## Second reading by N1

1. Compared the complete module with the repository using `diff`, and mechanically
   compared the original theorem signature: byte-for-byte identical. No existing
   definition, statement or public import changed; no accidental interface change.
2. Compiled every delivered module locally in import order, without warnings. Searched
   for forbidden constructs and checked the scratch-copy axiom output. The only sorry
   is the named geometric substatement listed above; no data or definition uses sorry.
   Verdict: a checked reduction conditional on the declared hole, not a completed proof
   independent of sorryAx.
3. Reviewed the new statement and its proof in words against Stacks Tags 0BLH and 05ER.
   It isolates the localized numerator-vanishing step; it does not assert an annihilating
   exponent. The main proof separately establishes the localization and clears the
   denominator. For f=0 or nilpotent f, W is empty and its section ring is zero; for
   empty covers the equalizer and zero-ring charts give the same conclusion. No new
   hypothesis is smuggled in. Repeated searches with different queries; Mathlib's
   basic-open localization lemmas apply to one scheme and do not give the matching
   comparison. The existing `puncturedMap_basicOpen_appTop_bijective` is a downstream
   consequence importing `PuncturedCompletionMatchingAffineSectionsComparison`, which
   imports this kernel theorem, so importing it here would form a cycle.
4. Read the proof from the item downward. Kept the valid principal-open transport and
   denominator-clearing argument, and removed the unnecessary added Mathlib import.
   The formal H0 route remains imported below the split. Checked
   `dag/units/sk-prop-input-spreading.json`: this supporting node is not named in its
   realized fields, and no unit statement, step or route is bypassed. No module is pruned.
5. Checked both node records against the Lean signatures and the proof. Their
   proof_deps equal the union of their steps' uses. The new node has its source,
   self-contained statement, searches, provenance, blueprint, chapter/unit and exact
   lean record; its blueprint tag now agrees. Corrected the item's DAG steps to
   distinguish image/localization, geometric vanishing and elementary zero clearing.

Changed during second reading: moved the split statement to its own module; expanded
its proof docstring and node; fixed its blueprint tag; completed the searches; changed
`letI` to `let`; removed the unused added Mathlib import; corrected the item's DAG proof
steps and this report's hole accounting. The original public theorem signature and the
valid localization argument were preserved.
