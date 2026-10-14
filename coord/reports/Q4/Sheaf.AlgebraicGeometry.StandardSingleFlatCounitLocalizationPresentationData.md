## What changed

Implemented `AlgebraicGeometry.standardSingleFlatCounit_localization_presentation_data`
in its original module, with its original signature and docstring. The proof chooses
both affine opens from the affine basis, checks the containment, proves base-open
restriction flatness by explicit section scalar-action calculations, proves source-open
restriction flatness in a private helper, and applies `h_affine` to the top restriction.
It keeps the same bounded flat complex and composes both presentation isomorphisms.
A private categorical helper combines the two equations without unfolding large derived
functors. This avoids the heartbeat exhaustion of direct rewriting; no compile time
limit or heartbeat limit was raised in the delivered files.

Added the proof-only import `Sheaf.AlgebraicGeometry.StandardSingleBaseChangeTopRestriction`
for the remaining source-isomorphism comparison. The public import is unchanged.
The current module compiles without warnings in approximately 11 seconds.
The new statement module compiles without warnings in approximately 6 seconds.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.standardSingleFlatCounit_localization_presentation_data`
(node `lem-pc-standard-single-flat-counit-localization-presentation-data`).
There are no sorries left in the item's module; both private helpers are proved.

Added one hole:
`AlgebraicGeometry.standardSingleBaseChange_topRestriction_comparison`
(node `lem-pc-standard-single-base-change-top-restriction`), in
`Sheaf.AlgebraicGeometry.StandardSingleBaseChangeTopRestriction`.
This is a decomposition, not a net reduction in holes: one closed, one added.
The remaining theorem asserts only top-source isomorphism transport of the single
comparison. It has no affine hypothesis, point, relative flatness, choice of
neighborhoods, bounded flat complex, or presentation assumption. Its docstring and node
specify the canonical construction and equation, including empty schemes and zero modules.
Its source comparison lives on the base before derived pullback, which is necessary to
compose the presentation's base direct-image identification.

## No longer needed

None. No original imports, nodes, or modules were removed. The original affine
localization route and unit are retained. No global presentation or stalk calculation
is needed in this module, and no such proof modules were added as imports.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the statement or its planned argument was found. The original
single DAG step hid the top-source normalization calculation; it is now a separate node.
The existing `exists_derivedBaseChange_source_iso` theorem cannot directly supply this
interface: its existential source isomorphism is only between objects after derived
pullback, rather than the image of an isomorphism on the base. The source-open unit
naturality statement retains the necessary normalized source map, but using it here
still requires the single-coefficient composition and canonical pullback-apex bridges.
These are spelled out in the new node's proof plan. No existing declaration was changed.

The blueprint ancestor script returned `None` for the item; the new node follows the
existing item's recorded localization ancestor instead. Searching the whole blueprint
for `top open` found no duplicate statement. Mathlib searches were performed through
msearch: LeanSearch was unavailable; LeanFinder returned only underived pullback tools;
Loogle found identity restriction, and grep found no matching Mathlib comparison.

## New nodes

`lem-pc-standard-single-base-change-top-restriction`, in
`dag/nodes/sec-picard-framework/`, isolates compatibility of the canonical single-module
base-change map with the top-open source isomorphism, retaining a base-level source
isomorphism and the commuting equation. This is strictly the final transport step of
the original proof. The unchanged K, its boundedness and flatness, both affine choices,
both flatness restrictions, and the assembly of the presentation are handled by the
proved caller. No change records or forced adaptations are required.

## Second reading by Q4

1. Compared the delivered existing module with the repository using diff and checked
   the existing theorem signature byte for byte: identical. Its docstring, universe,
   public import, options and visibility are unchanged. There are no changed public
   definitions, forced adaptations, or interface change records. Verdict: pass.
2. Compiled both modules in import order through lcompile.py: no errors or warnings
   (5.2 and 9.1 seconds). Scratch copies with #print axioms checked both private
   helpers and both public theorems. The helpers use only propext, Classical.choice
   and Quot.sound; the public theorems additionally use sorryAx from open statements.
   The only delivered sorry is the named top-restriction theorem listed above.
   No forbidden declaration forms or definition holes occur. The existential
   witnesses are eliminated inside a proof of a proposition, never used to define
   arbitrary data. Verdict: pass, one-for-one decomposition, net holes zero.
3. Read the top-restriction statement and its complete docstring argument against
   the pinned single-map definition, the single-map composition theorem, the
   source-open unit naturality theorem and the apex transport theorem. Its source
   isomorphism is on B before Lg*, which is necessary for the caller. The two
   isomorphisms have the correct directions. Exact restriction along the top
   inclusion and its base change, adjunction units and right-adjoint composition
   mates construct these comparisons; coefficient composition and apex transport
   give their equation. Zero modules and empty sources require no extra hypotheses;
   identity base maps require no cancellation of the base-change arrow. There is
   no assumption of affine presentation or relative flatness in this remaining
   lemma. It is strictly the final transport step, not a restatement of the item.
   Independently searched Mathlib with msearch leanfinder, loogle and grep using
   Beck--Chevalley/isomorphic replacement and pullback isomorphism queries, and
   searched both library roots for top/source transport and restriction flatness.
   The derived source-iso theorem only exposes an isomorphism after Lg*, the
   open-top theorem only concludes invertibility, the apex theorem changes only
   the fibre-product apex, and the right-adjoint normalized transport theorems
   concern second mates with additional qcqs hypotheses. None supplies this
   statement directly. Closing the remaining coefficient/source normalization
   would require more than a short repair. Verdict: pass.
4. Read the proof top downward: affine-basis choices, explicit scalar-action
   restriction of relative flatness, application of the supplied affine hypothesis,
   and categorical composition of the presentation equations. Both imports are
   needed, and the newly added transport import is proof-only. The sole original
   proof dependency is retained, so No longer needed = none is complete. The unit
   sk-thm-picard-coherence has empty realized attachments in this checkout; this
   delivery changes none and retains the recorded localization ancestor and route.
   Verdict: pass.
5. Checked both JSON nodes against the Lean signatures, source/docstring plans,
   blueprint ancestry, chapter and unit. The existing node changes only proof,
   proof_deps and proof_origin. Its dependencies are exactly the union of uses;
   the new node has all required creation, search, source and Lean fields and its
   proof_deps agree with its two proof steps. Verdict: pass.

Second reading changed only this report, adding independent review and validation
results. No mathematical or Lean repair was needed; no additional holes were closed
or added during the second reading.
