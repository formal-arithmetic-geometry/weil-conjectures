# Stage 1 report: lem-trf-point-quotient-augmentation-diagram

## Files written

- dag/nodes/sec-trace-formula/lem-trf-point-quotient-augmentation-diagram.json: statement, split; statement unchanged; not a Mathlib leaf.
- citations.json: one verbatim statement quotation for every use in every proof step.
- report.md: this report.

No new nodes and no new Mathlib leaves. The sandbox initially contained only dispatcher brief markers; there was no split or delivery to recover. The interrupted search result was recovered from searches.jsonl. Existing imported searches were retained, and this run's actual queries and results were appended.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and the quotient/augmentation terminology. The unrelated Koszul augmentation declarations do not state this item. Generic Roos declarations, including DerivedLimitTowerProperty.lean, do not state the completed coefficient quotient augmentation with its point sections and representative comparisons.

## WANTED

None. The supporting sources are present.

## Findings and corrections

The imported statement is retained. The source blueprint clause (3) only describes the integral derived-limit realization; the explicit normalized representative diagram is an agent refinement, not a theorem quoted verbatim from that blueprint. The proof is accordingly marked agent-written. Read its entire proof, Stacks Tag 0941 (sites-cohomology.tex, lemma-derived-limit-is-ok, including its proof), and Bhatt--Scholze Definition 3.5.2 on PDF p.24 and the surrounding Proposition 3.5.1. The latter distinguishes completed coefficient sheaves from constant coefficients and defines the natural reduction-completion map for arbitrary complexes. No equivalence between all pro-etale sheaves and ordinary modules is used: only exact final-object evaluation on the algebraically closed point is used.

The ambiguity of an arbitrary isomorphism filling a Roos triangle is avoided by giving an actual two-coordinate chain isomorphism and using the specified localization comparison in the statement. The signs of the two cone conventions were checked by substitution: (x,y)=(a,-b) gives (d a,-d b-(1-s)a) in the corresponding order, hence exactly the requested differential after reordering. This was written explicitly in Step 7.

No unfinished work remains in the one-level split. Below it, already-existing non-Mathlib nodes remain their owners' items.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs to distinguish. Searched the entire blueprint with blueprint_refs.py search for 'quotient augmentation', 'sections completion', and 'Roos', and searched the DAG for the same concepts. The two imported matches for the first search concern reconstruction of complete inputs, whereas this item is an unbounded representative computation without completeness. Existing generic nodes were reused rather than duplicated. In particular the strict quotient unit adjunction lemma concerns the actual reduction/realization adjunction, which is stronger and differently normalized data than needed here; the present statement already specifies its quotient augmentation by its chain representative.

## Review by Q77

I checked the statement and each proof step against the actual statements of every cited node, not against a construction hidden in its proof. Every citation in citations.json is copied from the statement field as read. The proof is an assembly and explicit calculation using existing smaller results, not a replacement of the item by a new lemma restating its conclusion.

Step 1 uses the actual sheaf tensor definition and strict Roos model. The tensor unit r_n commutes with the quotient map because 1 maps to 1; both the differential identity and the naturality equation are stated and computed. The universal property extends those pure-tensor identities to sheaves. In the signed differential the extra term is -(1-s)r, which is zero. This is an elementary calculation, and no preservation of quasi-isomorphisms is claimed here.

Step 2 uses clause (1) of lem-weil-integral-scalar-extension-well-defined with Y=s and L=E. That clause explicitly applies to quasi-isomorphisms between flat-term K-flat complexes, all of which are hypotheses here, and explicitly includes the whole strict cone, not merely its separate reductions. The identity field extension is allowed. Exact sections and their preservation of quasi-isomorphisms are explicit in lem-weil-point-proetale-sections-exact. Passing from Gamma(R_s)-modules to O_E-modules leaves the underlying cohomology unchanged. Neither clause assumes completeness or boundedness.

Step 3 uses the actual sectionwise product assertion of lem-weil-proetale-countable-products-exact and the explicit two summands in def-weil-strict-roos-model. I verified the intertwining equation by the nth projection, so the comparison really commutes with the signed differential and all strict tower maps. It is the canonical product comparison, and its inverse is specified degreewise; there is no chosen triangle filler. This identifies the map of Step 2 with H(D(u)), proving its quasi-isomorphism invariance.

Step 4 uses the explicit signed homotopy formula of lem-pur-strict-roos-homotopy-functor, including the required transition compatibility: h tensor 1 commutes with the coefficient quotient maps. The FIRST assertion of lem-weil-pbc-site-derived-tensor-descent explicitly states the equivalence from localized flat-term K-flat homotopy complexes to D(R_s); its later bifunctor assertions are not used. Thus there is no unsupported assumption that a resolving subcategory is already a localization. Parts (1) and (2) of lem-weil-pbc-localization-universal-property supply both descent of the functors and descent of their transformations. Exact sections invert quasi-isomorphisms on the source as required. The sites are used in the fixed project universes, so the localization equivalence has the stated size hypotheses.

Step 5 uses the actual defining strict quotient construction of def-weil-integral-scalar-extension. The statement of this item fixes chi as represented by v_P and iota as the specified localization comparison including q; hence the whole-arrow equality iota chi [q]=[v_P] follows from that specification and the descent already checked in Step 4. Applying the Step 3 coordinate isomorphism gives exactly a_P. This step does not identify derived arrows from their separate tower evaluations. The isomorphism assertion for m uses exact sections, not an assumption that chi itself is invertible. Thus arbitrary incomplete K is included.

Step 6 uses the natural representative comparison explicitly asserted by lem-weil-integral-scalar-extension-well-defined and the localization universal property. I wrote the induced chain-map equality and the inverse-arrow cancellation used for roofs. This verifies naturality for derived morphisms and the identity comparison between two representatives, not merely for a single strict chain map. The map is diagonal on BOTH product coordinates.

Step 7 uses lem-cbc-exact-product-functor-strict-limit, whose statement explicitly supplies the specified strict-limit comparison and its independence of resolutions. Exact countable products in the source are furnished by the cited pro-etale product node. The target is O_E-modules, realized as module sheaves on the small one-object trivial site, where surjectivity of products is the coordinatewise choice of lifts. Exactness and the canonical product comparison are the ones checked earlier. The signed-coordinate change was checked directly. The scalar-extension lemma computes all levels and their actual transitions on the same P; the final claim concerns the entire derived tower rather than independent objects at each level.

I checked zero complexes, identity maps, constant complexes in a single degree, identity coefficient extension, and a potentially incomplete K. The zero shifted coordinate satisfies the chain equation even when quotient maps are not flat: the relevant quasi-isomorphism assertion is about K-flat inputs and is supplied by the cited theorem. Nothing asserts invertibility of the augmentation for incomplete objects. Unbounded complexes require only exact countable products and the cited unbounded K-flat localization results; no truncation argument is hidden. I checked the cited nodes' dependency closures and none reaches this item, so their reuse introduces no cycle. There are no proof steps over 2000 characters and no new statements to small-case audit.

The off-unit statement citations are generic tools: point evaluation, exact products, K-flat localization, integral scalar-extension invariance, signed Roos homotopies, and exact-product-functor strict limits. They implement clause (3) of the unit's node route without replacing a unit step; each is declared in split_report.tool_uses. No SGA source is cited.
