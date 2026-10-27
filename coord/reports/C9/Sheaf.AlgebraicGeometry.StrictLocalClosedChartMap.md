## What changed

Implemented `AlgebraicGeometry.Scheme.strictLocalClosedChartMap` from the individual
pointed affine chart models. Its statement and the existing
`StrictLocalClosedChartRingData` structure are unchanged.

Added `Sheaf.AlgebraicGeometry.StrictLocalClosedChartModels`, isolating precisely the
individual chart-model comparison of the old proof's Step 1. Its record contains the
two base-ring actions, presentations, strictly henselian structures and specified residue
identifications. It contains no map from C to D and no quotient of C.

The item now proves chart compatibility by cancelling the open immersion and applying
Spec faithfulness; proves base compatibility by localization extensionality; proves the
residue equation from the unique canonical map's pointed equation; and proves locality
by reflecting units through the specified residue identification. It then constructs the
actual quotient action and algebra map using two explicit quotient lifts, proves
uniqueness by quotient surjectivity, and proves locality and both maximal-ideal equations.
No data is selected in a definition from an unproved existence statement.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.strictLocalClosedChartMap`
(node `lem-trf-strict-local-closed-chart-map`). The item has zero remaining holes.

Added one hole:
`AlgebraicGeometry.Scheme.strictLocalClosedChartModels`
(node `lem-trf-strict-local-closed-chart-models`). Its complete source-based proof in words
is in its docstring and node. This is a decomposition, one hole closed and one added,
not a net proof. The canonical-map compatibility and quotient arguments are complete.

Validation: remote `lcompile.py --all` passed for both modules: the chart models in
3.9 seconds and the main theorem in 11.3 seconds. The original theorem signature and
ring-data definition were also checked byte-for-byte against the shared source. The
required delivery tool runs compilation and preflight again before pushing.

## No longer needed

Removed the item's private imports of
`Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison` and
`WeilConjectures.RingTheory.StrictHenselizationTriples`. Their nodes
`lem-exc-affine-strict-local-ring-comparison` and
`lem-weil-pbc-strict-henselization-triples` are no longer direct proof dependencies of
the item. They remain necessary for the new individual chart-model node; neither
module is claimed to be globally pruned. Removed these two entries from the item's
obsolete direct `tool_uses` list, retaining them on the new model node. Also removed
the unused private import `Mathlib.CategoryTheory.Limits.HasLimits`.

`def-weil-pbc-relative-separable-closure` and
`def-sc-ring-strict-henselization` are likewise used in the new model node rather than
as separate substantive steps of the assembly. The evaluation/colimit comparison from
the old Step 2 is supplied by the already proved unique pointed canonical-map
characterization, so `def-weil-pbc-category-colimit` is no longer a direct proof dependency
of the item. All existing public imports are retained. No module is withdrawn, and no
unit step or adopted source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The old Step 1 requires transporting two pointed presentations
across affine comparison isomorphisms, together with the localization and residue-field
identifications for R/IR. The existing comparison theorem takes a presentation as input;
it does not directly provide the simultaneous record requested here. That remaining
construction is now isolated explicitly. The rest of the original four-step argument is
implemented without strengthening any hypothesis.

The new statement was checked on I=0, nilpotent I, nonmaximal p, non-Noetherian A, and
Omega strictly larger than K. If I is the unit ideal or the quotient chart is empty,
there is no given geometric point x, so those cases are vacuous. None of these cases
requires a new hypothesis. The unit `sk-i-curve-zero` and its route are unchanged.

## New nodes

`lem-trf-strict-local-closed-chart-models` records the simultaneous individual chart
comparison, sourced to Stacks Tag 04HX and Algebra Tag 04GW. It is strictly a part of
the original argument: it asserts neither the prescribed map's base/residue compatibility
nor annihilation of IC, the S-action on C/IC, its unique factor map, locality, or its
maximal-ideal formulas. LeanFinder, LeanSearch, Loogle and Mathlib grep searches found
no matching theorem; the existing affine comparison and triples declarations are its
proof dependencies. A search of the DAG found no duplicate simultaneous model theorem.
No change record is needed: no existing signature or definition changes.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
