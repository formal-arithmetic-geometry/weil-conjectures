## What changed

The existing theorem
`AlgebraicGeometry.Scheme.Modules.resolutionSectionClass_open_restriction`
has a complete Lean proof from the new raw restriction computation
`AlgebraicGeometry.Scheme.Modules.restrictedResolution_open_cohomology`.
Its signature and the definition of `cohomologyOpenRestriction` are unchanged.
The new computation lives in
`Sheaf.AlgebraicGeometry.RestrictedResolutionOpenCohomology`, imported only for
proofs. There are no consumer adaptations or changes to existing public signatures.
The static checker classifies the added local proof attributes and scoped
elaboration options as an interface change; their locality is documented in
`coord/changes/resolution-section-open-restriction-local-options.md`.

A proved private helper `sectionClass_open_restriction` handles arbitrary opens:
`NatTrans.app_homology` commutes the section-complex map with the evaluation
homology isomorphisms, and naturality of `sectionCohomologyTheta` finishes that
square. The main proof identifies restriction of the pushed complex with
restriction of the original complex degreewise, composes the raw comparison
with this helper, and uses naturality of the inverse resolution comparison to
pass to the higher direct image. It then evaluates the morphism equality at y.

This realizes both steps of the existing plan rather than assuming the normalized
class restriction identity under another name. The remaining lemma has no scheme
morphism f, higher direct image, theta, evaluation-homology comparison, or
`resolutionSectionClass`: its conclusion is entirely before those operations.
The source argument is Stacks 01E2, 01FB and 01E4, read on the Stacks website.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.resolutionSectionClass_open_restriction`
(node `new-resolution-section-class-open-restriction`).

Added one strictly earlier hole:
`AlgebraicGeometry.Scheme.Modules.restrictedResolution_open_cohomology`
(node `new-restricted-resolution-open-cohomology`). It is a public named theorem
whose whole proof is `by sorry`, with a full augmented-lift proof in its docstring.
It compares raw section-complex homology for two arbitrary opens and is the part
of plan step 1 that the existing top-to-open computation does not state.

This delivery is a decomposition: one hole closed, one added, net zero holes.
The target module itself has no remaining `sorry`. The private helper is proved.
Both files compile through lcompile.py. Empty/equal opens, zero coefficients and
p=0 require no additional hypothesis or inversions: the same naturality and
inverse identities apply, and the raw lemma describes the usual restriction
map without requiring it to be invertible.

## No longer needed

No existing import was removed. The original public import is preserved so that
other importers see exactly the same interface.

The parent proof no longer needs
`lem-weil-pbc-higher-direct-image-presheaf` /
`Sheaf.Paper.HigherDirectImagePresheaf`: its universality and stalk assertions are
unnecessary for a restriction equation, which follows from naturality of theta.
The parent also does not use the top-only theorem
`lem-weil-pbc-restricted-resolution-cohomology` /
`Sheaf.AlgebraicGeometry.RestrictedResolutionCohomology`: the new raw lemma is
needed for two arbitrary opens, and a top-to-open equation does not permit
cancellation of a generally nonsurjective cohomology restriction map.
These are not imported. This is local pruning, not a claim that other targets
stop reaching these modules. The parent also no longer directly uses
`lem-weil-pbc-module-cohomology-fmap-functorial` /
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`; that node remains
needed below the new raw lemma (independence of augmented-lift choices).
The new parent proof_deps retain the section-class definitions and the new lemma.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The existing raw restricted-resolution theorem
covers top-to-open restriction only; the plan needs two arbitrary opens with
separate pinned identifications. That gap is now an explicit smaller item.
LeanSearch returned Internal Server Error; the report and node do not treat this
as evidence of absence. Lean Finder, Loogle and Mathlib/library grep were also run.
No short exact match was found. The unit's realization and route are unchanged.

## New nodes

`new-restricted-resolution-open-cohomology` in
`dag/nodes/sec-proper-base-change/` records the arbitrary-open raw computation,
its augmented-lift proof, source and search results, and its exact Lean signature.
It remains in the parent's unit `sk-thm-p1`. Existing statements, definitions and public imports are unchanged, and the new
module is a proof-only dependency. The change record
`coord/changes/resolution-section-open-restriction-local-options.md` documents
the added local proof attributes and scoped elaboration options, which the
static checker classifies as command-stream changes.

## Second reading by G1

1. **Unchanged visible declarations: pass.** Compared the entire delivered parent
   module with the repository using diff. The definition body and signature of
   `cohomologyOpenRestriction` and the complete signature of
   `resolutionSectionClass_open_restriction` are byte for byte unchanged. The
   sole extra import is plain `import`, since only the proof uses it. The added
   private theorem, local irreducibility attributes and declaration-scoped
   options change no exported statement or data; the change record documents
   the command-stream additions. No consumer module is adapted.
2. **Proof and axioms: pass.** Both files compile through `lcompile.py` in import
   order (7.5 and 34.6 seconds in the first review compile). Read the private
   helper's cancellation of the evaluation homology isomorphism and its use of
   `NatTrans.app_homology`; then checked theta naturality. In the parent proof,
   `subst U` removes the equality transport, the pushed restriction agrees
   degreewise by reflexivity, and the final sheaf naturality square has the
   correct direction. There is one new named public theorem with whole proof
   `by sorry`; there are no hollow definitions, hidden holes or forbidden
   declarations. Scratch-copy axiom checks are recorded below.
3. **Split statement: pass as a decomposition.** Read Stacks 01FB, 01E2 and 01E4
   on their websites, and the declarations of all six proof dependencies.
   The new raw equation is before evaluation homology, theta and the inverse
   higher-direct-image comparison; it does not restate the normalized equation.
   Its coefficient map includes the restriction-composition identification,
   and the section isomorphisms are pinned by `RestrictedResolutionSections.components`
   and augmentation, so arbitrary comparison automorphisms cannot alter the
   equation. The lift is the restriction unit followed by pushforward of t,
   where t is j^*R.comparison, restriction composition, then R'.comparison
   inverse. The two augmentation equations identify its coefficient map.
   Restriction preserves limits, and its right adjoint preserves injectives;
   independence computes the cohomology map using lambda = identity. Cancel
   resolution comparisons and use the pinned components to get I(U) -> I(L).
   For L=U this is the identity after comparison cancellation, including when
   R and R' differ. Empty L and zero coefficients give maps to zero. Degree
   zero gives ordinary section restriction; none of these cases needs a
   restriction map to be surjective or invertible. Independent Lean Finder
   search for derived-global-sections naturality along open immersions returned
   only underived open-immersion naturality tools; Loogle search for homology
   and mapHomologicalComplex returned no hits. Repository grep also found
   `moduleCohomologyFMap_of_augmentedLift` and the top-to-open
   `restrictedResolution_cohomology`: they supply tools, but neither gives
   the two-open pinned comparison without constructing its lift and proving
   its degreewise restriction equation. No exact existing statement was found.
4. **Route and pruning: pass.** The private lemma proves the second part of the
   old plan using Mathlib homology naturality and sheaf naturality; only the
   raw restriction part of the first step remains open. All three old parent
   proof dependencies no longer directly used are now explicitly named under
   No longer needed, with functoriality retained below the raw lemma. The
   existing public import supports the existing interface and is preserved;
   the new module's public import supplies its statement. Neither item node
   realizes a unit statement or step in `dag/units/sk-thm-p1.json`; its realized
   nodes and the chapter/unit route are unchanged.
5. **Nodes: pass.** The existing node differs only in `proof`, `proof_deps` and
   `proof_origin`. Its three steps match the raw comparison, proved evaluation
   and theta square, and final derived-resolution naturality square. The new
   node has its verbatim Lean signature, source, self-contained statement,
   six dependency citations, search records, creation and blueprint ancestry,
   chapter and unit. The union of step uses is exactly its proof_deps.

Second reading changed the parent's stale proof docstring, which named the
old top-only theorem and unused composition/naturality route, to the proof
actually written. It also made the raw lemma's augmented lift explicit in its
docstring and node, and completed the parent pruning list for functoriality.
No Lean signature, definition body or proof term was changed.

Scratch-copy axiom results: `sectionClass_open_restriction` and
`cohomologyOpenRestriction` use only `propext`, `Classical.choice`,
`Quot.sound`. The parent theorem and the raw split theorem additionally use
`sorryAx`, as expected from the recorded open raw equation. No other axiom
appeared. The scratch source was removed before delivery.
