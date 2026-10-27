## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-formally-etale-space-chart-locality.json: existing statement node, now split in six steps; Mathlib verdict no match. Statement and statement dependencies unchanged.
- citations.json: a verbatim statement quotation for every node citation in every proof step.
- searches.jsonl: actual msearch.py search records; the original item searches are retained in the node and the five searches of this delivery are appended.

There are 0 new nodes and 0 new Mathlib leaves. No Lean file, repository file, launcher file, unit or chapter record was written.

## Attachments

None. Searched lean/WeilConjectures for the blueprint id, formal etaleness, infinitesimal lifts and square-zero charts. The hits concern rings, schemes or other constructions, not the full algebraic-space criterion. No sorry declaration was treated as a proof.

## WANTED

None. The required Stacks sources are available locally.

## What was wrong or missing

The item was an unsplit statement with no proof. Its statement agrees with Stacks Tag 04GD, lemma-formally-etale (1) iff (2), after expanding formal etaleness according to Tag 049S, definition-formally-smooth-etale-unramified. There is no statement dispute or hypothesis change.

The proof of Tag 04CY, lemma-etale-on-top, omits the final descent details and has slips in its internal references to numbered parts. I use its actual construction, rather than those mistaken internal numerals: construct a lifted test atlas, prove uniqueness first, compare on arbitrary overlaps by affine restriction, and glue sections. No mathematical source assertion needed correction.

The blueprint ancestor command returns None for this inherited item, as its existing blueprint.from.node already records. I retained the inherited precise formal-chart provenance and via list, searched the imported blueprint for formal etaleness and infinitesimal lifting (no matching node), and kept same_as empty. I read the latest blueprint unit, its proof, and the direct-images statement and proof under literature/blueprint/latest/. The current direct-images proof is through proper/open direct images and compactification; the inherited chain describes a supporting algebraic-space prerequisite, not an instruction to replace that unit route. No unit realization is claimed by this foundational lemma.

## What could not be finished

Nothing in the requested one-level split. The pre-existing unsplit theorem lem-sfb-space-thickening-etale-scheme-equivalence is deliberately reused as a dependency and remains a separate item. It is strictly different from the current item: it lifts etale objects and maps across a thickening, rather than characterizing formal etaleness of an arbitrary morphism by compatible charts.

## Not duplicates

No new nodes. Reused the existing thickening-equivalence and compatible-atlas statements instead of creating representable-etale lifting, formal composition, or formal cancellation nodes. The latter claims are two- or three-line deductions explicitly carried by the proof steps.

## Mathlib searches

All five queries were actually run through the required msearch.py command and read. Loogle queried "AlgebraicSpace" and returned zero hits. Grep queried AlgebraicSpace|FormallyEtale in AlgebraicGeometry and returned zero hits. LeanFinder queried formal etaleness on etale scheme charts, then rephrased it as square-zero lifting under etale localization. The eight hits in each response concerned scheme etaleness, cancellation, formal unramifiedness or ring formal etaleness. LeanSearch queried descent of unique infinitesimal lifting along a surjective etale scheme atlas; it returned ring square-zero lifting, scheme etale objects and descent of other scheme properties. I read Mathlib/AlgebraicGeometry/Morphisms/Etale.lean:118-145 and Mathlib/RingTheory/Etale/Basic.lean:86-94 to distinguish these from the desired algebraic-space chart theorem. None is an exact match or a one-line generalization of the item. Exact queries, hit summaries and digests are recorded in the item and searches.jsonl; no service was unavailable.

## Review by Q36

I read the item source directly in literature/stacks-project/spaces-more-morphisms.tex: Tag 049S (definition-formally-smooth-etale-unramified), 04AL (lemma-representable-property-formally-property), 04CY (lemma-etale-on-top), 04G5 (lemma-formally-permanence), 04GD (lemma-formally-etale), and 05ZS (lemma-thickening-equivalence). I checked the tags against tags/tags. I also read the first-order definition and base-change statement in more-morphisms.tex. There are no new-node sources to review.

Step 1 uses def-trf-algebraic-space for the actual scheme-test definition of representable etale, not for a lifting theorem. The scheme E=T times_B A is etale over T by precisely that definition. The statement of lem-sfb-space-thickening-etale-scheme-equivalence explicitly gives bijectivity on morphisms between any two etale scheme objects. Apply it to T and E over T: the initial section extends as a morphism over T, so the extension is a section. Def-sbc-first-order-thickening explicitly says a square-zero closed immersion is a thickening. This proves the needed representable-etale lifting in a few lines, without citing the downstream etale-space lifting node, which would risk circularity. The test T here can be any scheme.

Step 2 is the sole elementary step. I checked the four equations separately: f x=v b, u a=x, v h a=v b, and the common reduction of h a and b. Uniqueness for v gives h a=b. Any competing lift projects to the same x by P(f), then equals a by uniqueness for u. All inputs are step 1 and the definition of P. The square need not be cartesian. There is no unrecorded cancellation lemma hidden here.

Step 3 reads only the final existence assertion of lem-sfb-unramified-etale-compatible-charts: for a prescribed surjective target atlas it supplies U,u,h with the required equality and u surjective. It does not infer formal etaleness from that node. The current hypothesis supplies P(h), and step 1 supplies P(v); lifting successively proves P(vh)=P(fu). Both uniqueness checks are explicit. I checked that the compatible-atlas node does not depend on this item.

Step 4 uses the scheme-test part of def-trf-algebraic-space to form W_0 and know it is surjective etale. The essential-surjectivity clause of the existing 05ZS node gives W over T and the stated reduction isomorphism; it does not promise a global atlas section. Surjectivity of W follows from the surjective composite W_0 to T. The local ring calculation C/IC with (IC)^2=0 proves first-order base change and affineness of each reduction directly. Open immersions are etale and etale maps compose by lem-weil-pbc-etale-composition-cancellation, clauses (1)-(2). Def-weil-etale-morphism gives flatness and local finite presentation, exactly the hypotheses in def-pc-fppf-site for a jointly surjective family to cover. These are all scheme maps, so no algebraic-space permanence theorem is being presumed.

Step 5 lifts c_0 over each of two candidate X-maps using step 1, then compares the U-maps using P(fu), which step 3 already established. Their equality gives equality of the X-maps on the cover. Def-trf-algebraic-space says X is an fppf sheaf, while def-weil-pbc-sites-and-cohomology explicitly states the sheaf equalizer and therefore separatedness. This is why the citation is to the sheaf definition rather than to a theorem about maps out of a quotient. I expanded the arbitrary-scheme uniqueness consequence by restricting to affine opens; open covers are fppf by the cited etale permanence node and the etale/fppf definitions. No separation or quasi-compactness hypothesis on the scheme is used.

Step 6 uses P(fu) on the affine tests of step 4. It compares the projected X-maps on the actual scheme overlaps W_lambda times_T W_mu, with the pulled-back reduction. The general uniqueness established in step 5 applies even if an overlap is not affine. The equalizer clause now supplies the glued X-section, and separatedness for Y and X verifies its two equations on the covering and its base change. The covering base-change assertion is among the site axioms explicitly stated in def-weil-pbc-sites-and-cohomology. Thus all gluing and equation checks are consequences of cited statements and the written preceding steps.

For B1-B10 I checked that there is no new object or theorem with a disguised proof, that the statement is self-contained, that notation and notions retain their existing definition dependencies, that TeX is encoded once, and that every source place uses a verified tag and label. No new Mathlib leaf or attachment is claimed. For C1-C8 I opened every cited statement, wrote citations.json from its exact text, kept proof_deps equal to the union of uses, and checked no selected dependency reaches the item. Scheme etale permanence is an existing Mathlib leaf, and is also declared as a generic tool use in split_report; no alternative unit route is used. For D1-D5 the entire chart-locality argument is in the item, with no new node restating either direction; the omitted source descent details are supplied. For E1-E7 I checked each source hypothesis, square-zero pullback, both equations in a lift, and every comparison object; no undocumented transport or equality of objects is used.

Edge cases checked: identity thickenings and zero ideals; empty T (the sheaf equalizer over the empty cover gives the unique section); empty X; empty Y, which forces X empty; disconnected tests; f the identity; and f:A^1_k to Spec k. In the last case P(f) fails on k[epsilon]/(epsilon^2), as it should, and the identity source/target charts witness failure on the right too. Nothing assumes etale f, finite presentation of f, finite atlas, separatedness, affineness of an atlas, or a global section of a surjective etale map. All non-elementary steps are shorter than 2000 characters. No SGA source was used.

The server review_split check passed with 0 new nodes before this report was written. The required delivery dry run and final push are run after the report.
