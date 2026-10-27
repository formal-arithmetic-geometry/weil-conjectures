## What changed

Replaced the proof hole of
`WeilConjectures.clopen_projective_chart_common_refinement` with the common-refinement
argument. The theorem's signature and all existing public imports are unchanged.
The proof intersects the two given covers, enumerates the product using
`finProdFinEquiv`, and proves covering, disjointness, closedness, compactness and
quasi-separatedness of the new members. It uses the existing normalized exact
`OpenCompletedRestriction.ordinary` functor. The coefficient-ring isomorphism
makes its unit map invertible, as checked on underlying abelian presheaves.
Termwise application preserves the strict bounds; the finite-product comparison
and unit identification transport both splitting maps and their identity equation.
Finally, `mapDerivedCategoryFactors` transports the chart isomorphism.

Added `Sheaf.Paper.ClopenCompletedRestrictionComparison`, isolating the remaining
comparison between the specified ordinary composite pullback and exact restriction
of the completed chart. This statement concerns a single complete complex and
nested clopens, with the restriction functor already defined. It asserts no
existence of a cover or projective model. Updated the item's proof plan and added
one node for the comparison. No existing shared definition, statement, attribute,
or public import was changed. All edits are inside the assigned item and its new
lemma/node.

Validation uses server-only `lcompile.py --all`; the delivery tool compiles both
modules and runs its axiom, statement, node and preflight checks before pushing.
No local Lake or whole-library build is run.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.clopen_projective_chart_common_refinement`
(node `lem-fix-clopen-projective-chart-common-refinement`).

Added one hole:
`WeilConjectures.clopen_completed_restriction_comparison`
(node `lem-fix-clopen-completed-restriction-comparison`), in its own module. Its
proof is exactly `by sorry`; its docstring gives the source and full argument.
There are zero holes in the item module and one in the new module.

This is a decomposition: one original hole closed and one strictly smaller
comparison hole added, for a net change of zero holes. The finite-cover geometry,
unit identification, strict bounds, finite-free retractions and assembly are
proved in Lean without further split-off statements. The remaining comparison
has no affineness, two-object, boundedness or projective-model hypotheses and
cannot itself supply any chart complex.

## No longer needed

The item does not need
`lem-weil-pbc-strict-perfect-ringed-pullback-model`
(`Sheaf.Paper.StrictPerfectRingedPullbackModel`). Restriction to an open is exact,
so its derived functor is computed termwise for every complex. In particular no
K-flatness argument or general strict-perfect ringed-pullback computation is
needed to preserve these models. The original proof-dependency module was not
imported in the item source; no existing import of it was removed.

The coefficient-comparison, clopen-derived-compatibility and ringed-derived-
monoidal-comparison nodes remain needed by the new comparison's plan. They are
not claimed as pruned. The item imports only the new comparison and the Mathlib
product and unit-map interfaces for its proof. Existing public imports remain.
No modules or upstream declarations are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned dependencies provide normalized clopen restriction and its
completeness properties, but their published restriction functors are not yet
identified with the exact `ordinaryIntegralDerivedPull` and
`integralDerivedPullback` used by this item. `ordinaryCompletedIntegralPullback`
requires Noetherian schemes, finite dimension, prime invertibility and
constructibility, none of which is assumed here. Likewise
`OpenCompletedRestriction.open_completed_restriction` requires prime
invertibility. Those theorems cannot be applied by silently adding their
hypotheses. The new comparison states precisely the missing clopen compatibility;
its source argument imposes no such extra hypotheses. The existing
`OpenCompletedRestriction.coefficients_exact`, by contrast, needs no prime
invertibility and supplies the actual exact functor used in the proof.

Small cases checked in the argument: either finite index can be empty (the
corresponding cover then forces the source empty); intersections and original
members may be empty; rank zero is permitted by the finite-product comparison;
zero complexes and identity inclusions obey the same isomorphisms. No nonempty
scheme, nonzero module, nonempty index or strict endpoint inequality is used.
The unit record `sk-rem-sf-pf-done` has no realized statement or proof-step nodes
for this item; its route is unchanged. No source-library files are changed.

## New nodes

`lem-fix-clopen-completed-restriction-comparison`, in
`dag/nodes/sec-six-functors/lem-fix-clopen-completed-restriction-comparison.json`,
realized by `Sheaf.Paper.ClopenCompletedRestrictionComparison`: comparison of the
ordinary composite pullback of a complex whose pullback to V is complete with
normalized exact restriction of its completed chart on U to a smaller clopen A.
The source is the restriction/refinement argument of Stacks Tag 09C3,
`lemma-local-structure-constructible-complex`, together with Tags 03D8, 06YY and
08TC. Its statement reuses the existing restriction-definition node
`def-pur-open-completed-restriction-data`. LeanFinder, Loogle and grep searches
were run; the results are recorded in the node. The blueprint search found no
existing blueprint node for this comparison. The new lemma is an interface
comparison step, strictly short of producing the common projective charts.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
