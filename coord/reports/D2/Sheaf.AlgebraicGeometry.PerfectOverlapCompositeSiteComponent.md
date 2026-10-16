## What changed

Proved both clauses of perfectOverlapCompositeSiteComponent using the existing
canonical site triangles, naturality and the explicit nested-site comparison.
Its statement is unchanged. The comparison constructor stores explicit gamma
maps, with fully proved normalization, coherence and uniqueness APIs identifying
them with the former localization lifts. The local-composite isomorphism retains
its construction behind no_expose and has a proved equation API.
The final stage-map comparison explicitly unfolds its named constructor.
Nested-square normalization is imported only for proofs by the gamma module;
its public import names the nested-square API used by its signatures.
This repair additionally relocates four existing public component theorems from
PerfectOverlapOpenSquareCube into PerfectOverlapObjectRealizationCoreComparisons.
NestedSiteCompatibility uses these imported theorems and no longer declares
private copies. No theorem signature or proof in the relocated API changes.
The current linter's six pre-existing letI warnings in the comparison component
proof are fixed with let; the cube component equation retains its existing
section instance under a scoped warning suppression. All seven modules compile;
the first full pass exposed only these pre-existing lint warnings. The constructor's
three direct users, the shared stage-map module and the parent's direct consumer
also compile unchanged against these fresh outputs.

## Proved and sorry left

Closed AlgebraicGeometry.perfectOverlapCompositeSiteComponent: one original hole.
Added holes: zero. Remaining holes in the seven delivered modules: zero.
The two rejected branch holes and their unlanded modules/nodes are removed.

## No longer needed

The four private duplicates of openPullbackRestrictionIso_inv_app_eq_square,
openPullbackRestrictionIso_hom_app_eq_square_inv,
perfectOverlapRestrictionBeta_hom_app_square and
perfectOverlapRestrictionBeta_inv_app_square are removed from
NestedSiteCompatibility; their public originals are shared through
CoreComparisons. No library module is globally pruned by this relocation.

The rejected PerfectOverlapCompositeSiteComponentFalse and
PerfectOverlapCompositeSiteComponentTrue modules and their false/true nodes are
removed. None landed in main. The constructor no longer builds gamma through
localization preimages. Its unused DerivedOpenRestrictionIsoDescent proof import
is removed. The obsolete direct public import of
DerivedOpenRestrictionLocalization is also removed from the constructor module;
it remains transitively available through CoreComparisons. Localization remains
needed for the uniqueness proof; the nested square and canonical site triangles remain needed. No blueprint unit is bypassed.
Removed direct parent proof imports: PerfectHomComparisonTriangle,
DerivedOpenRestrictionLocalization, DerivedPullbackComposition,
PerfectOverlapNestedPullbackSquare, PerfectOverlapObjectRealizationCoreComparisons,
and TwoOpenComparisonDiagram. Their required APIs remain used transitively;
no global pruning of those nodes is claimed.

The following old parent proof dependencies are removed from its direct
`proof_deps` (their APIs remain in the proved helper route where needed):

- lem-pc-perfect-overlap-nested-pullback-square
- lem-pc-ringed-spaces-derived-pullback-composition
- lem-pc-perfect-hom-comparison-triangle
- def-pc-two-open-comparison-diagram
- lem-pc-derived-open-restriction-is-localization
- def-pc-perfect-overlap-core-comparisons-api

The constructor no longer uses lem-sc-derived-open-restriction-iso-descent as a
proof dependency. No existing library module is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The latest return identified four private statements in NestedSiteCompatibility
that duplicate existing public theorems in OpenSquareCube. The copies are
removed. Directly importing OpenSquareCube would cycle through the repaired
Transport constructor, so the existing four theorems are moved unchanged into
CoreComparisons, which both modules already publicly import. This is a relocation
of the single existing API, not another proof or a renamed duplicate. See
coord/changes/D2-shared-open-square-components.md.

The returned split merely relabelled the original clauses and was not a reduction.
This repair proves the clauses from genuine comparison APIs. The computational
constructor is repaired rather than splitting the proof. Changes are recorded in
coord/changes/D2-explicit-nested-site-gamma.md and
coord/changes/D2-fixed-comparison-interfaces.md. The original shared stage-map
and stage-equivalence interfaces are retained. The retained new-node records
lacked LeanSearch entries; the real search and its verdict are now recorded.
The gamma signature record now begins at `def`, matching the declaration parser;
the Lean declaration remains noncomputable.

## Forced adaptations

PerfectOverlapRestrictedComposition is unclaimed. Its original proof fails at line 42 with
`Tactic unfold failed to unfold perfectOverlapCompositeLocalIso`, because that
implementation is now hidden. Replace it with the proved local-iso
equation; unfolding compositionTo and reflexivity remain. Existing signatures
and visibility are unchanged. Scoped warning suppression preserves the existing
unused section instances, and one unused simp argument is removed.

## New nodes

lem-pc-perfect-overlap-nested-pullback-normalization records the fully proved
normalization theorem in PerfectOverlapNestedPullbackNormalization.

def-pc-perfect-overlap-nested-site-gamma records the explicit comparison and its
fully proved inverse-component, coherence and uniqueness APIs in
PerfectOverlapNestedSiteCompatibility. Neither module has a hole. The relocated component API is recorded under the
existing def-pc-perfect-overlap-core-comparisons-api node; it creates no new
node or obligation. The separate
module is needed before the constructor, avoiding the downstream cube import cycle.


The component-API relocation is recorded in
coord/changes/D2-shared-open-square-components.md.

## Second reading by D2

1. Signature and visibility review: PASS. Compared all seven delivered modules
   with the shared repository. The declaration parser reports no changed
   existing signatures. The four component declarations relocated from
   OpenSquareCube to CoreComparisons have identical statements, proofs,
   docstrings and visibility; their original surrounding instance binders are
   retained. The two definition/interface changes are covered by the three
   change records above. No target statement is changed. Independently compiled
   the original RestrictedComposition against the delivered dependencies: it
   fails at line 42 when unfolding perfectOverlapCompositeLocalIso, exactly as
   the forced-adaptation record states.
2. Proof and axiom review: PASS. Independently compiled all seven modules using
   lcompile.py --all, with no errors or warnings. The parent took 57.5 seconds;
   every other file took at most 33.7 seconds. Scanned all delivered Lean for
   sorry and forbidden declarations: none occur. A separate scratch module
   printed axioms for all 52 public declarations of the delivery, including
   the parent, the explicit gamma and its coherence/uniqueness API: each uses
   only propext, Classical.choice and Quot.sound. No construction chooses data
   from an unproved existence theorem.
3. New statements and reuse review: PASS. There are zero split-off holes. Read
   both new helper modules completely: normalization is a genuine nested-square
   identity, while gamma is a real composite of existing isomorphisms with
   proved component, coherence and uniqueness equations. The arguments use
   categorical identities without assumptions on points or nonempty opens,
   so empty opens, identity inclusions and zero objects are covered. Repeated
   library/upstream searches with nested-restriction terminology and fresh
   LeanFinder, Loogle and Mathlib grep queries for faithful precomposition,
   counit naturality and functorial composition. The hits provide the generic
   APIs already used; no existing exact fixed-comparison theorem was found.
   The four previously duplicated component results now have one public owner.
4. Route and pruning review: PASS. The parent combines the existing canonical
   site triangles with explicit nested gamma, functoriality and naturality;
   neither new helper restates either parent clause. Public imports in the new
   modules are needed by their statements or definition bodies, and the
   normalization import in NestedSiteCompatibility is proof-only. Checked the
   old proof_deps against No longer needed: all six removed parent edges and
   the removed constructor descent edge are listed. These are direct-edge
   removals, with no claim of globally pruned modules. The unit
   sk-thm-picard-semicon and its realized fields are untouched; no unit route
   is bypassed.
5. DAG review: PASS. Read all five delivered node records against the Lean.
   Every proof_deps set equals the union of the proof steps' uses. Existing
   records change only lean, proof, proof_deps and proof_origin. The two new
   nodes carry the source, complete proof plan, searches, creation provenance,
   blueprint ancestry and matching Lean declaration records required by the
   stage-3 brief. The relocated API is included in the existing core-comparison
   node; there is no additional obligation for it.

Second-reading changes: appended this independent review and recorded fresh
search evidence. No Lean, node or change-record correction was necessary.
Closed holes: AlgebraicGeometry.perfectOverlapCompositeSiteComponent (one of
one original holes). Added holes: none. Split off: zero. Globally pruned: none.

Consumer validation: the unchanged CanonicalGammaLocal, CompositeObjectPin,
CompositeStageMap, CanonicalCounitU and ObjectRealizationCoreOfData modules all
compile cleanly against the delivered artifacts. CoreOfData was retried after
the dry run finished rebuilding its sandbox dependencies; the retry passes
without warnings. The first attempt overlapped that rebuild and reported a
missing temporary dependency artifact rather than a Lean proof error.
