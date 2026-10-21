# Q136: lem-sf-package-localization-projection-realization

## Files written

- dag/nodes/sec-six-functors/lem-sf-package-localization-projection-realization.json: statement, split into nine proof steps; Mathlib has no matching theorem. The statement and original metadata are retained unchanged.
- citations.json: a verbatim statement extract for each of the 26 step/node citations.
- report.md: this report. searches.jsonl contains five actual searches made with the required launcher command; the item retains its inherited search records and adds these searches.

New nodes: 0. Mathlib leaves: 0. No unit file, Lean source, repository file or launcher file was written. make_split.py and finish.py are sandbox-only preparation scripts.

## Attachments

None. The exact blueprint tag is absent from WeilConjectures. The notion search found WeilComplex.exists_distTriang_derivedLowerShriek_structure_openClosed in lean/WeilConjectures/WeilSheaf/OpenClosedTriangle.lean, lines 53–105, and the finite-stage projection/package structures in SixFunctors/Etale/Derived/Package.lean. The former is a structure-morphism result for Weil complexes, and neither gives the item's strict integral tower with all transitions, coefficient-stage comparisons, and projection clause. They do not establish an exact attachment for this item.

## WANTED

None.

## Problems found and changes

The item was an unsplit extracted obligation with no proof. Its current main-20261015 blueprint parent explicitly obtains clause (3) by applying compact-support image to recollement, and clause (5) from fix-prop-projection-formula. I followed those two sentences. The DAG unit record still quotes the older package numbering (projection in (3), orientation in (5)); this does not change the current parent route, and no unit record was edited.

A levelwise family of distinguished triangles is insufficient to identify an integral connecting arrow. The proof now uses the existing exact tower-valued functor before taking total inverse limit. It does not infer equality of derived morphisms from equality of reductions. I also compare the finite connecting maps before compact-support image, where the existing recollement theorem supplies uniqueness; uniqueness of the image triangle is neither assumed nor needed.

The statement is unchanged; no STATEMENT-DISPUTED correction was needed. The Weil qualification is read with the cited definition, which defines Weil structures at the field coefficient stages. The result concerns equivariance of the underlying triangle and does not assert that the category of fixed pairs itself is triangulated.

## Searches and reuse

Whole-DAG searches by recollement, strict towers, Roos, derived inverse limit, and projection formula located the existing inputs. I ran tools/blueprint_refs.py ancestor on the item and search on recollement, localization triangle, and projection formula. The ancestor is prop-functor-package; no blueprint node states the combined strict-tower realization and projection assertion in this item. The existing all-stage triangle and projection theorem were reused, rather than recreated as nodes.

The required command ran LeanFinder with two different phrasings, Loogle on CategoryTheory.Functor.IsTriangulated, grep on recollement|projectionFormula|projection_formula|strictTower, and LeanSearch with the complete adic compact-support question. All services returned successfully. I read every returned hit: the semantic results concern generic derived-category fractions, ordinary scheme module adjunctions, sheaf-condition cone equivalences, and other unrelated constructions. Loogle returns generic triangulated-functor preservation; I read Mathlib/CategoryTheory/Triangulated/Functor.lean, lines 183–191, which gives IsTriangulated and map_distinguished. This does not supply the geometric operations, their coherent strict quotient tower, or the projection theorem. There is no exact match or one-line specialization for this item. The inherited Q92 searches are preserved, including the unsuccessful old identifier query and its corrected query. No search was invented or marked absent because a service failed.

## Not duplicates

No new nodes are proposed. In particular, no new node restates the recollement-image clause, the projection clause, exactness of total limit, or the finite-Tor preservation facts; all already exist.

## Review by Q136

I read coord/delivery-errors.md B–E in full, the stage-1 brief and stage document, SETUP.md's three route levels, GOAL.md, the chapter and unit records, and the actual main-20261015 parent statement and proof. For the mathematics I read main-20261015/sk-prop-sf-localization/prop-sf-open-closed-triangle-all-stages.proof.md, the main-20261015 projection-formula proof, and the representative-independence proof under sec-six-functors-basics/sk-thm-sf-pf-field. I checked Stacks derived.tex Tag 0152 (lemma-derived-canonical-delta-functor), sites-cohomology.tex Tag 0941 (lemma-derived-limit-is-ok), and proetale.tex Tags 09AH and 09BM (open–closed sequence and exact closed direct image). I also read Bhatt–Scholze, Definition 6.7.6, Lemma 6.7.7, Remark 6.7.8 and the start of Lemma 6.7.14 in the local PDF. The separately derived compact-support composite is essential: it is not replaced by the derived functor of the underived composite. No SGA source is used. There are no new-node sources to review.

I opened and read the statement of every node actually cited. The following is my mathematical check of each step, not a claim that a reference's proof supplies extra unstated facts.

1. prop-sf-open-closed-triangle-all-stages explicitly supplies the bounded constructible triangle with the counit, unit, functorial third arrow, uniqueness and field-stage equivariance. The item has exactly its separated finite-type schemes, complementary immersions, and coefficient stages.
2. lem-compact-support-direct-image-triangulated is explicitly a finite pro-etale theorem for one compactification and the same finite coefficient ring. def-compact-support-direct-image-detailed identifies the open functor at the identity proper compactification. lem-sf-package-compactified-tower-comparisons supplies composition, proper coincidence, and compactification comparison on precisely these stages. thm-sf-ctf-stability clauses (i), (iii), (iv) ensure the vertices lie in the finite-Tor categories. I wrote the three conjugation formulas, with the shift comparison in the third; this is the isomorphic-triangle axiom of def-weil-triangulated-category, rather than a new lemma.
3. lem-pur-derived-change-of-rings really asserts an exact derived scalar functor, including nonflat quotient maps; no underived tensor exactness is used. lem-fix-operation-reduction includes pullback, the two direct images, and preservation of units and counits on the stated domains. The first and third finite vertices and first two maps therefore agree with the finite recollement theorem. That theorem's uniqueness identifies the third map. This argument takes place on X before applying compact support.
4. lem-weil-compact-support-reduction-tower-functor states an exact R-linear functor to the derived strict tower category, evaluation on morphisms as well as objects, and the precise m-to-n quotient-induced transitions. These are exactly the facts required for all three arrows to constitute one coherent triangle. Its hypotheses allow our fixed field, schemes, compactification, completed coefficient sheaf and integral complexes.
5. lem-weil-pbc-ringed-strict-tower-homotopy-limit explicitly states exactness of total Rlim on strict towers. The integral operation definition uses the same fixed compactification, reductions, scalar restrictions and quotient transitions. Taking the limit of the coherent functor from step 4 realizes that definition on maps as well as objects. The sibling compactified-tower-comparisons theorem supplies the completed composition/proper identifications including transitions. I retained the third arrow as the total-limit image with its shift comparisons; I did not choose it by TR3 after taking the limit.
6. lem-sf-integral-compact-support-constructible states completeness and a single finite interval independent of n for each input in Dbc. It applies separately to A, B, C, all provided by the first theorem. Their three intervals may be replaced by their minimum lower endpoint and maximum upper endpoint if one common interval for the whole triangle is desired. lem-weil-integral-constructible-triangulated explicitly makes the inclusion exact; no uniform bound over all possible inputs is asserted.
7. def-weil-rationalization-karoubi explicitly makes raw localization exact, preserving the integral distinguished triangles. prop-weil-pbc-rational-transport is an exact raw localization transport theorem for supplied R-linear exact functors and actual natural transformations; the preceding steps have supplied those. lem-fix-operation-reduction supplies the rational operation identifications. lem-weil-scalar-extension-exact-triangulated gives exactness for finite E-subset-L extensions. The algebraically closed coefficient definition specifies common-stage triangles and morphism equality, and prop-weil-pbc-descent-functors descends compatible transformations and equations. Hence this step preserves the connecting map, not only an isomorphism class of objects.
8. I checked U empty, Z empty, X empty, and K zero. Every cited theorem allows these; the recollement triangle degenerates to an identity triangle, and all exact functors and scalar passage preserve its zero vertex. For a descended Weil input, prop-sf-open-closed-triangle-all-stages gives equivariance of all three original maps and lem-fix-weil-operations explicitly gives equivariance of compact-support operations and composition comparisons. The fixed-pair definition specifies only E and Qbar coefficients; no integral Weil convention is added.
9. fix-prop-projection-formula has exactly K bounded constructible and L bounded constructible finite Tor, with composition, compactification, finite reduction, scalar extension and proper coincidence. Its map is the canonical projection transformation. def-weil-derived-pullback-tensor-hom explicitly defines the integral pullback and tensor by completed reduction towers. Thus the last step neither weakens the input domains nor claims a projection formula for nonproper ordinary direct image.

For B I verified that no new statements, definitions, Mathlib leaves or duplicate nodes were manufactured. For C I matched every step's uses against the cited statement and wrote verbatim excerpts in citations.json; proof_deps is their union, and no cited dependency reaches this item. For D the localization proof actually applies exact functors and writes all three maps; the projection theorem is a pre-existing black box explicitly named by the blueprint. For E I checked the finite versus completed coefficient categories, the fixed compactification across all n, the direction of a and b in the conjugation formulas, the shift in the connecting map, quotient-map compatibility, field-stage representatives, and empty-stratum cases. No step exceeds 2000 characters, and no hidden long-step lemma was left inside one. The only external-unit inputs are declared as tool uses in split_report; they are generic tools or the exact existing blueprint inputs, not a replacement route.

## What remains unfinished

No part of this item's stage-1 split remains unfinished. Existing unsplit dependencies remain obligations of their own nodes; this delivery creates none. Server dry-run and push results are recorded below when available.

## Validation

The initial server dry run exited 0 and printed OK (not pushed) at 67238e28472. I then added the explicit raw-localization definition citation to step 7 and its verbatim quote, and requested a final dry run before push.
