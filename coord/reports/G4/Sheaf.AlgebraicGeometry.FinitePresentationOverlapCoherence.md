## What changed

Reduced `AlgebraicGeometry.exists_finitePresentation_overlap_eventual_coherence`
without changing its signature. Its proof obtains coherence at the limit by
cancellation in the supplied comparison, obtains diagonal and universal triple
equations at a common stage, extends those equations to every test scheme by
pullback naturality and the threefold pullback universal property, and preserves
the supplied limit comparison under the prescribed refinement.

Added `Sheaf.AlgebraicGeometry.FinitePresentationOverlapChartEquations` for the
remaining geometric step. It asserts only the equations on finitely many diagonal
and threefold test charts, with no global limit module and no comparison conclusion.
Its plan uses the existing `finitePresentation_zero_map_descent` on the difference
maps, followed by a finite common upper bound. This avoids rebuilding affine module
presentations and scalar-extension comparisons already handled by zero-map descent.

Added `Sheaf.AlgebraicGeometry.OverlapComparisonRefinement`, with a complete proof
of `AlgebraicGeometry.nonempty_overlap_comparison_refinement`. It constructs the
map between the two limit covers with `pullback.lift`, pulls the given comparison,
uses Mathlib's restriction/pullback and identity isomorphisms, then transports
through raw pullback composition in both directions. The private composition
calculation follows `DescentData.pullFunctorCompIso` but does not require coherence
of the original stage transitions. All five private categorical helpers are proved.

The upper module imports all three new modules only for proofs. The universal-test argument is proved separately in
`Sheaf.AlgebraicGeometry.OverlapUniversalTestCoherence`; its
`AlgebraicGeometry.coherent_of_universal_tests` has no geometric hypotheses.
The upper module's private `overlapLimitMap_stage_comp` is also proved. No existing
public interface, target signature, definition, or visibility changes. No forced
adaptations. The unit route is preserved; its realized statement and steps are empty
in the unit record, and this remains the same Noetherian-approximation subargument.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.exists_finitePresentation_overlap_eventual_coherence`
(node `lem-pc-fp-overlap-eventual-coherence`). The upper module contains no `sorry`.

Proved `AlgebraicGeometry.coherent_of_universal_tests`
(node `lem-pc-overlap-universal-test-coherence`) with no `sorry`, as well as
the additional categorical theorem
`AlgebraicGeometry.nonempty_overlap_comparison_refinement`
(node `lem-pc-overlap-comparison-refinement`) with no `sorry`.

Added exactly one hole:
`AlgebraicGeometry.exists_finitePresentation_overlap_eventual_chart_equations`
(node `lem-pc-fp-overlap-eventual-chart-equations`). This is the whole proof of one
public named theorem in its own module, with source and a complete proof in words.
It is strictly the finite-stage chart-equation portion of the original argument.
The extension to arbitrary test schemes, cone-map composition, and comparison
transport are proved independently and combined in the upper module.

This is a decomposition: one old hole closed, one new hole added, net zero holes.
It does not claim that the upper theorem is independent of `sorryAx` yet. The
comparison-refinement theorem is proved using only the permitted standard axioms.

Edge cases: an empty chart index has vacuous diagonal and triple equations and
comparison components; the chosen threefold lifting argument is invoked only for
actual indices. Zero modules cause zero difference maps. No antisymmetry or
nonempty index assumption is added: k supplies nonemptiness, and the zero-map
descent theorem already treats directed preorders. Pullback objects supplied by
the chart lemma are determined by their universal properties up to canonical
isomorphism; no arbitrary object is defined from an unproved mere-existence claim.

## No longer needed

Second reading narrows the two new modules' `DescentDataPrime` imports to `ChosenPullback`; the broader descent-prime interface is unnecessary. This does not claim global pruning of that Mathlib module.

Removed the upper module's proof import `Sheaf.Algebra.FinitePresentationColimit`
and its direct proof edge to `lem-pc-fp-module-map-descent-affine`. The remaining
chart theorem's proof plan instead uses
`Sheaf.AlgebraicGeometry.FinitePresentationZeroMapDescent` and
`lem-pc-fp-zero-map-descent`; its placeholder proof does not import the unused module. This is a replacement of the immediate route,
not a claim that the algebraic module has become globally unreachable: other
arguments still use it. No whole module is claimed globally pruned.

No overlap-map lifting or new choices of transitions are needed here. In particular
`Sheaf.AlgebraicGeometry.FinitePresentationOverlapMapLifting` and
`lem-pc-fp-overlap-map-lifting` are not imported by this delivery. They remain needed
by the parent local-model argument and are not claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The plan's mathematical route is retained. Its affine equality clause cannot be
applied directly to the raw all-test-schemes transition structure: one needs the
geometric identification of the finite diagonal/triple test schemes and their
module maps. The new chart statement isolates precisely that missing interface.
The existing scheme-level zero-map descent theorem already provides the vanishing
step, so the new plan reuses it rather than repeating affine algebra descent.

The comparison transport uses raw transitions at the original stage. Mathlib's
`pullFunctorCompIso` applies to genuine descent data; using it directly on T would
assume the stage coherence being proved. The private raw composition calculation
avoids that assumption. Genuine descent data are used only after pulling to the
limit, where the supplied comparison proves coherence.

Duplicate check: searched the full blueprint using `blueprint_refs.py search
'overlap cocycle'` and `search '01ZR'`, the full DAG by overlap/coherence phrases,
and the library by declarations and concepts. The three blueprint cocycle matches
are Nagata scheme gluing maps, not module transition maps. The new chart theorem
is not `lem-pc-fp-overlap-eventual-coherence`: it has no comparison conclusion and
only universal chart equations; the categorical extension and comparison proof
are separate. It is not `lem-pc-fp-overlap-map-lifting`, which constructs maps
rather than stabilizing specified ones, nor `lem-pc-fp-local-overlap-models` or
`lem-pc-fp-local-descent-datum`, which construct genuine descent data. It is not
`lem-pc-fp-zero-map-descent`, which treats one specified global map on one specified
base-change model; this lemma must construct and identify the finitely many
chart defects and make their equations simultaneous. It is not
`lem-pc-fp-module-map-descent-affine`,
`lem-pc-preorder-module-map-equality-descent`, or
`lem-pc-finite-family-module-map-equality-colimit`: those are ring/module statements
and have no scheme test-chart identification. The other source-tag matches concern
objects, presentations, complexes, flatness, support, maps, or sections; none states
either new theorem. `def-pc-local-overlap-transitions` defines the objects and proves
cancellation, but contains no comparison-refinement theorem. The new refinement
theorem needs no inverse-limit or finite-presentation hypotheses at all.

The LeanSearch service returned Internal Server Error; this is recorded as
unavailable. LeanFinder, qualified Loogle, and source grep were run with msearch.py
and their actual results are in searches.jsonl. Read Stacks Tags 01ZR and 05N7
at their source URLs and read Mathlib's DescentData and ChosenPullback sources.
The additional universal-test search returns no exact theorem; qualified Loogle
finds `ChosenPullback₃.exists_lift`, which its proof uses. Source grep finds no
existing raw universal-test coherence declaration.
No unsupported source claim or new axiom is introduced.

## New nodes

`lem-pc-fp-overlap-eventual-chart-equations`, in
`dag/nodes/sec-picard-framework/lem-pc-fp-overlap-eventual-chart-equations.json`,
states the finite-stage universal tests. It retains the original finite-model
hypotheses and prescribed canonical refinement; its one hole is the remaining
geometric assembly from existing zero-map descent. Its source is Tag 01ZR (3),
whose first proof reduces to Tag 05N7.

`lem-pc-overlap-comparison-refinement`, in
`dag/nodes/sec-picard-framework/lem-pc-overlap-comparison-refinement.json`, states
and proves the generic scheme-cover comparison transport. Its source is the
composition/naturality part of Tag 01ZR's first proof, implemented using Mathlib
pseudofunctor associativity and restriction descent isomorphisms.

Updated the original node's proof, proof_deps, and proof_origin to match the Lean
assembly. No statement or definition changes; no change record is required.

`lem-pc-overlap-universal-test-coherence`, in
`dag/nodes/sec-picard-framework/lem-pc-overlap-universal-test-coherence.json`,
states and proves extension from diagonal and chosen triple tests to coherence
on every test object, for an arbitrary Cat-valued pseudofunctor. It has no hole.
This extracts the original private calculation into a reusable small module.

## Second reading by G4

1. Compared every delivered module with the repository version. Existing declaration signatures and visibility are unchanged; the new declarations are recorded in the accompanying DAG nodes. Verdict: pass.
2. Compiled all four delivered Lean modules with `lcompile.py --all`. The only remaining `sorry` is the named chart-equations theorem listed above; no forbidden declarations or hollow definitions occur. Verdict: pass, with the documented split hole.
3. Checked the new statements against their hypotheses and edge cases. The chart-equations theorem is strictly weaker than the original coherence target, while the universal-test and comparison-refinement results are independently proved and appropriately scoped. Verdict: pass.
4. Reviewed proof routes and imports. The upper proof uses the chart, universal-test, and comparison-refinement modules; the former finite-presentation-colimit import is removed and documented as unnecessary. Verdict: pass.
5. Checked DAG proof/proof_deps/proof_origin records and the unit route against the Lean proofs. The records agree, and no unit step is bypassed. Verdict: pass.

Second reading replaced the broad public import `Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime` in the chart-equations and universal-test modules with `Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback`. Their signatures need the chosen pullback types, and their proofs do not use the descent-prime interface. No statement, definition, or forced adaptation changed. The delivery remains a decomposition: one original hole is closed and one strictly simpler named hole remains.

The scratch `#print axioms` checks show only `propext`, `Classical.choice`, and `Quot.sound` for the comparison-refinement and universal-test theorems. The upper theorem and chart-equations theorem additionally use `sorryAx`, exactly as expected for the one remaining hole. Fresh independent LeanFinder, qualified Loogle, and grep searches were run with different queries; no existing finite-stage chart-equations theorem was found. The qualified categorical search finds `pullFunctorCompIso`, which requires genuine descent data and cannot directly handle the raw incoherent transitions. Checked [Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR) and [Tag 05N7](https://stacks.math.columbia.edu/tag/05N7) directly against the proposed reduction.
