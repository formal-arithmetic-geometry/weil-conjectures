## What changed

Replaced the sole sorry in `Sheaf.Paper.EtaleCEFilteredTotalConstruction` by a complete
Lean reduction to two independent stages, without changing its theorem signature.
The proof obtains presentations, first-page maps and filtered augmented lifts from
`EtaleCECoherentFirstPageLifts`, obtains stationary comparisons for the same presentations
from `EtaleCEStationaryPageNaturality`, and instantiates the latter with the explicitly
conjugated sections lift. The representative equation is the precise interface between
the two stages; it does not assume the desired stationary-page equation.

The new stationary module defines `EtaleCEQuotientRealization` as a type of isomorphisms
with existing concrete cycle/boundary cokernels, and `EtaleCEPageMapOnRepresentatives` as
an explicit equality on maps from arbitrary abelian-group test objects. These contain
no choices, postponed construction data or sorry. The first new theorem concerns only
first-page maps, strict augmentation and filtered lifts; the second concerns only
stationary comparisons and arbitrary filtered sections-total maps. Each is a strict
part of the original argument. Updated the original DAG proof and added their nodes.

All three modules compile together through `lcompile.py --all`, without errors or
warnings. The existing signature is textually identical. The original theorem locally
disables the unused-variable linter because its unchanged existential signature includes
proof/binder names used only through dependent types; no signature was renamed.

## Proved and sorry left

Closed the original direct hole:
`AlgebraicGeometry.Etale.exists_etaleHypercohomology_ce_filtered_totals`
(`lem-weil-pbc-ce-filtered-total-construction`). Its combination proof has no sorry.

Added exactly two direct holes, each the complete proof of its named public theorem:

- `AlgebraicGeometry.Etale.exists_etaleCE_coherent_first_page_lifts`
  (`lem-weil-pbc-ce-coherent-first-page-lifts`), in
  `Sheaf.Paper.EtaleCECoherentFirstPageLifts`.
- `AlgebraicGeometry.Etale.exists_etaleCE_stationary_page_comparisons`
  (`lem-weil-pbc-ce-stationary-page-naturality`), in
  `Sheaf.Paper.EtaleCEStationaryPageNaturality`.

This is a decomposition: one upper hole closed and two lower holes added, not a
sorry-free proof. Existing dependency holes are untouched. No sorry in any definition.

## No longer needed

Removed these five direct proof imports from the original module:

- `Sheaf.CategoryTheory.CartanEilenbergFunctorial`
- `Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`
- `Sheaf.Algebra.Homology.FilteredComplexZBDescription`
- `Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison`
- `Sheaf.CategoryTheory.CartanEilenbergExists`

These are moved to the first new theorem's proof plan, not pruned from the argument.
Their respective nodes `lem-weil-pbc-cartesian-eilenberg-functorial`,
`thm-sp-spectral-object-yields`, `lem-sp-filtered-complex-ZB-description`,
`lem-weil-pbc-sheafH-ext-derived-comparison`, and `lem-sp-cartan-eilenberg-exists`
remain needed there. The original direct proof dependencies are now the two new nodes
and `lem-weil-pbc-ce-total-sections-comparison`; its former dependencies remain needed
below these stages or through the presentation interface. No whole module or node is
claimed as globally pruned. Its existing public import is unchanged.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies provide objectwise presentations and quotient isomorphisms,
and the bounded filtered-complex theorem requires a uniformly finite filtration.
They do not by themselves specify compatible simultaneous page-homology choices or
natural stationary comparisons for these degreewise finite totals. In particular,
one cannot choose unrelated witnesses from `exists_hypercohomology_firstPage` and
then infer page-map coherence. The first new theorem explicitly retains compatible
quotient realizations and their representative equations. The second theorem supplies
the separate natural stationary comparison; arbitrary isomorphisms from the objectwise
stable-quotient theorem alone do not prove its naturality.

Checked edge cases before stating the reductions: negative complex-degree bounds,
total degrees below that bound, zero complexes, empty schemes, and empty diagonals.
The degreewise bounds b and n+1 still apply; in a zero total top and bottom coincide.
Changing representatives by the next filtration step gives the same graded class,
and the representative predicate consequently imposes no artificial condition on
such lifts. For r beyond both tails, actual cycles generate the stable quotient.
No extra finiteness, nonemptiness or torsion assumption was added.

No unit route is bypassed: `dag/units/sk-prop-h2.json` has empty realization lists,
and this decomposition retains the original CE construction and convergence steps.
The Stacks TeX files cited by the nodes are absent from this read-only clone; their
listed sources were checked via the official pages
[015J](https://stacks.math.columbia.edu/tag/015J),
[015K](https://stacks.math.columbia.edu/tag/015K),
[012K](https://stacks.math.columbia.edu/tag/012K),
[012Q](https://stacks.math.columbia.edu/tag/012Q),
[012W](https://stacks.math.columbia.edu/tag/012W),
[0130](https://stacks.math.columbia.edu/tag/0130), and
[0132](https://stacks.math.columbia.edu/tag/0132).

## New nodes

`lem-weil-pbc-ce-coherent-first-page-lifts`: source is Stacks Tags 015J, 015K and 012K,
original steps 1–4. Constructs the simultaneous presentations, signed first-page maps,
strict augmented lifts and maps on cycle representatives. It claims no stationary
comparison or abutment-step map. Semantic search found injective-resolution naturality
lemmas but no exact theorem; Loogle found homologyMap_comp, and source grep located the
existing CE and filtered-page APIs. LeanSearch returned Internal Server Error.

`lem-weil-pbc-ce-stationary-page-naturality`: source is Stacks Tags 012K, 012Q and 012W,
original step 5. For an arbitrary fixed presentation family and quotient realizations,
constructs natural stable comparisons for every filtered sections-total map with the
representative property. It claims neither existence of a CE lift nor its first-page
cohomology formula. Semantic search found no exact comparison; local grep found the
objectwise degreewise stable quotient theorem, which supplies the quotient description
but not the displayed naturality. LeanSearch was unavailable. No change record is
needed: no existing signature, definition or public import changed, and no other
existing module was adapted.

## Second reading by S1

1. **Statements and accidental changes.** Compared the delivered target module with the repository version. The theorem signature is byte-for-byte unchanged; only imports, the proof, and a local linter option differ. The two new public theorem statements and the two helper definitions are exactly the interfaces used by the target proof. Verdict: pass.

2. **Compilation and axioms.** Compiled all three modules with `lcompile.py --all`; they compile without errors or warnings. The target contains no `sorry`; the only remaining holes are the two named split theorems listed above. Their use is the sole source of `sorryAx` in the target's axiom report. No axiom, unsafe, opaque, extern, or implemented_by declaration was added. Verdict: pass.

3. **New statements.** Checked the two split-off statements against their docstrings, DAG nodes, and edge cases (zero complexes, empty schemes and diagonals, negative bounds, and stationary tails). They are strict reductions: the first constructs compatible first-page data and augmented lifts, while the second handles stationary comparisons and arbitrary filtered sections-total maps. Neither restates the target. Definitions contain no postponed data. Verdict: pass.

4. **Pruning and route.** The target proof uses only the two new theorem nodes and the existing sections-comparison node. Five direct proof-only imports were removed from the target; the first split theorem retains the underlying route and dependencies. The unit `sk-prop-h2` remains the route, with no bypass of its CE construction or convergence steps. Verdict: pass.

5. **DAG agreement.** Updated the target node's proof and proof dependencies to match the proof, and added complete nodes for both split theorems with sources, proof plans, Lean declarations, and unit/chapter metadata. Verdict: pass.

Changed in this second reading: added this review section to the report only; no Lean statements or proofs required repair.
