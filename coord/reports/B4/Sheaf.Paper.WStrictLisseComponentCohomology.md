## What changed

Reduced `AlgebraicGeometry.ProEtale.CondensedRing.wstrict_lisse_component_cohomology`
by implementing the geometric and lisse parts of its current DAG plan in Lean.
The proof bundles the given homeomorphism, obtains the two compatible hypercovers
from `wstrict_common_component_hypercovers`, extracts the affine and w-contractible
instances and component homeomorphisms in each degree, checks the component-map
equation, restricts the lisse module using `isLisseCoefficientModule_upperStar`, and
extracts the bijectivity clause of `component_lift_lisse_section_comparison`.
It then applies the new acyclic-hypercover criterion and composes with the two
canonical isomorphisms already present in the definition of the section map.
The original statements, public imports, definitions, and adjunction-unit maps are unchanged.

Added `Sheaf.Paper.ComponentHypercoverUnitCriterion`, with one public theorem,
`AlgebraicGeometry.ProEtale.CondensedRing.componentHypercoverUnitCriterion`.
This is the remaining interface bridge from the existing sectionwise-module
normalization theorem to the actual internal-module derived unit. It assumes
explicit compatible hypercovers, weak contractibility and termwise bijective
section maps, and has no lisseness, affine, w-strict locality or component
homeomorphism assumptions. Its docstring gives the full proof and explains the
localization, unit compatibility, cochain inverse, normalized descent and
cancellation steps. This is a proper part of the argument: the parent constructs
all of its geometric hypotheses and proves its termwise bijectivity hypotheses
from independent existing declarations.

Updated the parent node's proof and proof dependencies and added the matching node
for the criterion. No other existing module or node is changed. No definition
repair or consumer adaptation is involved.

Validation: `lcompile.py --all` compiled both delivered Lean files, with exit code
zero. The criterion took 36.5 seconds and the item took 49.9 seconds, each below
the 60-second limit. All delivered Lean lines are at most 100 characters. All
referenced DAG dependencies exist, and the new node records the exact Lean signature.

## Proved and sorry left

Original item: two holes. One original hole is closed by decomposition, not counted
as a complete proof independent of newly added holes:
`AlgebraicGeometry.ProEtale.CondensedRing.wstrict_lisse_component_cohomology`
(node `lem-sfb-wstrict-lisse-component-cohomology`). Its assembly proof contains no
`sorry` and uses the two existing geometric/lisse comparison declarations and the
new criterion.

One original hole remains untouched:
`AlgebraicGeometry.ProEtale.CondensedRing.componentLisseSectionsPullback_comp`
(node `lem-sfb-wstrict-lisse-component-cohomology`). Its source and natural-language
proof are still in the original docstring.

One hole is added:
`AlgebraicGeometry.ProEtale.CondensedRing.componentHypercoverUnitCriterion`
(node `lem-sfb-component-hypercover-unit-criterion`). Its entire proof body is
`by sorry`. This is the general acyclic-hypercover descent and internal/sectionwise
normalization step; no data is chosen from it.

Thus the delivered item has one textual hole, the added module has one, and the
packet closes one original hole and adds one lower hole: net zero. This is a
decomposition. Empty schemes, zero modules, rank zero, negative cochain degrees,
and the degree-zero matching cone are included in the stated criterion and its
proof in words.

## No longer needed

Removed all thirteen old private proof imports from the item:

- `Sheaf.Topology.StoneanCover` (`det-pe-stonean-cover`);
- `Sheaf.RingTheory.StoneanCoverSecondStage` (`det-pe-wc-cover-second-stage`);
- `Sheaf.AlgebraicGeometry.ProEtale.WeakContractibleEquivalences`
  (`det-pe-weak-contractible-equivalences`);
- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`
  (`det-prop-sfb-module-pullback-exact-main`);
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteProjectiveDualizable`
  (`lem-proetale-finite-projective-dualizable`);
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`
  (`lem-sfb-internal-module-operations-transport`);
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
  (`lem-sfb-ringed-derived-monoidal-comparisons`);
- `Sheaf.Paper.ProfinitePointPullback` (`lem-weil-pbc-profinite-point-pullback`);
- `Sheaf.Algebra.Homology.LocallyFreeDerivedHom`
  (`lem-weil-pbc-ringed-site-locally-free-derived-hom`);
- `Sheaf.CategoryTheory.SiteFiniteBasisHypercoverExistence`
  (`lem-weil-pbc-site-finite-basis-hypercover-existence`);
- `Sheaf.Paper.ComponentRelativeProfiniteSite`
  (`lem-zl-component-relative-profinite-site`);
- `Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation`
  (`lem-zl-condensed-wcontractible-lisse-evaluation`);
- `Sheaf.CategoryTheory.Sites.ContractibleDerivedSectionsTensor`
  (`lem-zl-contractible-derived-sections-tensor`).

These are no longer direct proof imports of the assembly module. The common
hypercover and lisse comparison declarations encapsulate their relevant geometric
and duality steps; the new criterion names its actual remaining transport and
normalization dependencies. This does not assert that these modules are globally
unreachable or authorize deleting any declaration. In particular, the still-open
composition clause retains its planned ringed-derived and normalized-descent
inputs in the parent node. No global module withdrawal or unit-route change is
claimed. The three new private proof imports of the item are precisely the
criterion, common hypercovers and lisse inverse image modules.

## Where the brief, the DAG or earlier work was wrong

The item's Lean docstring expands the older nine-step proof, while its current DAG
already factors that argument through the common-hypercover and lisse-section
comparison statements. The implementation uses the current factored DAG.

The existing `AcyclicHypercover.pullback_normalization` is stated for sectionwise
ringed-site modules, simplicial objects over a chosen terminal object, and its
own single-complex localization conventions. It cannot be applied directly to
`componentLisseSectionsPullback`, which uses internal modules and the library's
singleFunctor comparison. The new criterion records this interface and
localization work explicitly, rather than identifying the maps by an arbitrary
isomorphism. Its proof uses the existing normalization statement, internal module
operation transport, coefficient section localization, and weakly etale site
localization as generic tools. The last three include other units; they support
the canonical-module/site interface and do not replace the unit's direct-image
route. No mathematical statement is disputed or weakened.

## New nodes

`lem-sfb-component-hypercover-unit-criterion`, in
`dag/nodes/sec-six-functors-basics/lem-sfb-component-hypercover-unit-criterion.json`,
records the generic acyclic-hypercover criterion, its exact Lean signature, full
proof in words, Stacks Tag 09A2 source, and LeanSearch, LeanFinder, Loogle and grep
searches. It isolates the parent's cochain/descent glue; constructing common
component hypercovers and proving the degreewise lisse comparison remain explicit
in the parent's Lean proof. There are no change records because no other existing
module, definition or statement was changed.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
