# Q70 — lem-coef-frame-pushout-product

## Files written

- `dag/nodes/sec-six-functors/lem-coef-frame-pushout-product.json`: statement, now split in five steps; statement unchanged; Mathlib verdict no match.
- `citations.json`: ten step/node pairs, each quoting the cited node's statement verbatim.
- This report. `searches.jsonl` records the six new searches made by msearch.py; `prepare.py` is a sandbox-only preparation script.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter file changed.

## Attachments

None. Searched the slopmaster2 project's `WeilConjectures/` by the item id, pushout-product, Reedy, and cosimplicial/frame spellings. There is no project declaration stating this result. The exact master source is not used as evidence of a completed proof.

## WANTED

WANTED: Hovey, *Model Categories*, Propositions 3.1.5, 3.6.8, 5.4.1 and 5.4.3, printed pp. 74–75, 99 and 130–131, for lem-coef-frame-pushout-product. The PDF at the item's source URL was read online (especially PDF pp. 108 and 139–140); it is not archived in `literature/`. No download or change to literature was made. Accordingly `proof_origin.by` is `agent`.

## Findings and split

The item was statement-only, not a finished split. Hovey 5.4.3 confirms the exact statement, including a Reedy cofibration between frames on cofibrant objects and the orientation of the pushout. No statement correction or dispute is needed.

Hovey's proof first establishes cofibration by 5.4.1, applies the simplex-collapse test 3.6.8 to each frame tensor, and finishes using a pushout and two-out-of-three. The split follows that route. For the first part I use the existing parametrized-adjunction lifting theorem: tensoring a boundary identifies with the latching object, so against any trivial fibration the simplicial corner map has boundary lifting. It is a simplicial trivial fibration; adjunction then proves the required corner arrow is a cofibration. This writes the generator reduction directly, without creating a separate node for a clause of the item. The existing boundary-and-collapse test supplies the substantial horn-filtration argument from Hovey 3.6.8.

The current blueprint ancestor was read at `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`, paragraph 2. Its derived coefficient-adjunction mapping calculation is the inherited ancestry of this source-frame tool; this item is not the unit's key node. Its historical ancestry and unit binding are preserved. Blueprint searches for pushout product, cosimplicial frame, cosimplicial, framing, latching and skeletal found no same-statement imported node. DAG statement searches found the existing collapse test and corner lifting nodes, which are reused, and the weighted-coend filtration and interval tensor nodes, which are unnecessary here.

Fresh Mathlib searches were made only through msearch.py, using LeanFinder twice with different phrasings, LeanSearch, Loogle, and two greps. The returned model-category closure instances do not state a framing theorem. The Cech conerve hits have different objects. `Mathlib/AlgebraicTopology/Reedy/Basic.lean` leaves the model structure as TODO. The generic monoidal arrow pushout product at `Mathlib/CategoryTheory/Monoidal/PushoutProduct.lean:72` is a construction, not this model-category assertion. All inherited search records were retained and all fresh records use the exact logged tool/query. No new node requires a separate search packet.

## Not duplicates

No new nodes. The proof reuses lem-coef-parametrized-adjunction-corner-lifting, lem-coef-simplicial-boundary-collapse-test and lem-coef-lifting-class-closure rather than creating versions of them. The Joyal and simplicial-set cartesian pushout-product nodes concern different tensors and are not replacements for this arbitrary-model-category frame theorem.

## Review by Q70

I read Hovey 5.4.1 and 5.4.3 with their proofs and 3.6.8 online, the current blueprint paragraph above, and the full statements of all six cited DAG nodes. There are no new nodes whose sources need separate review.

Step 1 uses the latching indexing category actually defined in lem-coef-reedy-model-structure. The boundary identification is justified by compatible face data: each other boundary simplex factors through a proper face, so its value is forced. The tensor adjunction is supplied in the item's statement. Preservation of colimits is written as its universal-property argument, not assumed as an uncited model theorem. Degree zero gives two initial objects.

Step 2 uses exactly the lifting equivalence stated in lem-coef-parametrized-adjunction-corner-lifting. I checked its pinned Mathlib declaration, `CategoryTheory.ParametrizedAdjunction.hasLiftingProperty_iff`, in lines 164–172 of `CategoryTheory/LiftingProperties/ParametrizedAdjunction.lean`, with the bifunctor and natural-adjunction hypotheses in lines 30–40. The first category is the full category of cosimplicial objects, not merely a category of frames; the second is simplicial sets and the third is M. All pushouts and pullbacks exist. For every n, Step 1 identifies the left corner with the precise relative latching formula in lem-coef-reedy-model-structure. Its model-category definition includes lifting of cofibrations against trivial fibrations. Crucially E and F need not be fibrant: no mapping-space theorem limited to fibrant targets is used.

Step 3 takes the boundary characterization of a simplicial trivial fibration verbatim from lem-coef-kan-quillen-right-proper. The same node supplies its Kan–Quillen model structure, hence lifting of the given simplicial cofibration i against that trivial fibration. Applying the corner-lifting node a second time yields the desired lifting against arbitrary ground trivial fibrations; the converse lifting characterization in the Reedy node's ground-model definition makes the pushout-product a cofibration. This uses statements, not a dependency's proof.

Step 4 applies lem-coef-simplicial-boundary-collapse-test with all hypotheses verified: all small colimits are preserved by Step 1; every boundary map is a latching cofibration; the simplex collapse equals the augmentation component because that augmentation is the identity in degree zero. The definition of frames in lem-coef-cosimplicial-frame-mapping states that each augmentation component is a weak equivalence. Thus the test applies separately to A and B, and to the given monomorphism/weak equivalence i. No simplicial enrichment or left properness is assumed.

Step 5 uses precisely pushout closure of a left lifting class from lem-coef-lifting-class-closure. The ground model definition identifies trivial cofibrations with the left lifting class of all fibrations. The cobase-changed map is B tensor K to P, not A tensor L to P. Its composite with the desired corner arrow is B tensor i, so two-out-of-three from lem-coef-reedy-model-structure has the correct orientation. The cofibration part was already proved in Step 3.

I checked B–E of delivery-errors: each new mathematical fact is either an existing cited statement or a universal-property calculation written in the steps; no new unsplit or duplicate nodes, no relabelled clauses, no uncited stability theorem, no circular citation, no off-unit tool use. Transitive dependency inspection of every cited node found no path back to the item. The ten quotes in citations.json are actual substrings of the current cited statements. All proof steps are under 1000 characters, and none hides a separate standard lemma.

Small cases checked: n=0 gives the initial latching object and tests lifting of f in degree zero; K=L makes the corner an isomorphism; K=L=empty gives an identity on the initial object; a trivial cofibration with empty domain must have empty codomain, so no spurious nonempty initial attachment is required. Taking f to be the identity also gives an isomorphism, while an initial source frame specializes the argument to the usual single-frame tensor result. These checks preserve all hypotheses. The item statement and all protected fields are unchanged. No Lean source was written or compiled, and no forbidden source route was used.

## Unfinished

None at the mathematical splitting level. The required dry run and direct delivery are performed after this report is written; their output is the delivery record.
