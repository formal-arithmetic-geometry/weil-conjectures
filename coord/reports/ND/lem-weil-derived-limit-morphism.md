## Worker report

Files written:
- dag/nodes/sec-proper-base-change/lem-weil-derived-limit-morphism.json: statement, split into three explicit elementary steps using existing definition nodes; not a Mathlib leaf.
- citations.json: one verbatim statement quotation for each step/node citation.
- searches.jsonl: search command's actual records; report.md: this report.

New nodes: none. New Mathlib leaves: none.

Attachments: none. Searching WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 by the blueprint tag, derived-limit words, homotopy-limit words and triangle-completion name found no declaration proving this exact assertion for arbitrary tower morphisms and both fixed connecting maps. HomotopyLimit.lean:108-130 proves exists_iso only for the same tower, not this assertion; of_iso changes towers by an isomorphism, and map acts by a triangulated functor. These are not attachments. The master checkout was treated only as reference material.

WANTED: none. All sources needed for the proof are local.

The imported statement is retained. Its source is Stacks Tag 0H9J, remark-functoriality-derived-limit in derived.tex, specialized to m(n)=n, when both product maps are the ordinary product of the level maps. The sentence about nonuniqueness is the source's warning that uniqueness is not asserted, not a claim that every instance admits two different maps (zero towers certainly do not). The proof has the same existential content and retains that warning. No statement dispute or route change was needed. The old node had no proof; the revised one spells out the middle square and the signs in the rotated triangles.

The item's nearest blueprint ancestor is def-weil-derived-limit. I read its original blueprint file, its DAG definition, the chapter record sec-proper-base-change and unit sk-thm-properbasechange. The blueprint gives the Roos triangle; this helper establishes its noncanonical morphism construction and does not replace any step of the proper-base-change unit. The original blueprint's displayed f_{n+1} versus declared f_n indexing is already resolved by the DAG definition; all equations in this delivery use f_n:K_{n+1}→K_n.

Searches: tools/blueprint_refs.py ancestor and searches for TR3 and derived limit were read, together with whole-DAG searches for 0H9J and triangle completion. No existing blueprint node duplicates this tower-morphism statement. All new Mathlib searches were made through msearch.py with their exact logged queries. First LeanFinder phrasing returned homology-sequence and homotopy-category material; the second phrasing returned CategoryTheory.Pretriangulated.complete_distinguished_triangle_morphism₁ and related lemmas. Loogle also found that declaration. The logged grep located it in Mathlib/CategoryTheory/Triangulated/Pretriangulated.lean:189, and I read lines 189-201. It takes a commutative square as a hypothesis, whereas the present item must derive that square from the tower morphism: this is not an exact or one-line specialization of the whole node. LeanSearch returned HTTP Internal Server Error and is recorded as unavailable. The generic lemma is not made into a new leaf because the existing triangulated-category definition already states TR2 and TR3, and their short application is written in full in steps 2-3.

Nothing remains unfinished. No Lean was written and no compiler, Lake or build tool was run. Only the required packaging dry run is used after this report. No push is requested; the sandbox is for a fresh second reader.

## Not duplicates

No new nodes. The whole-DAG 0H9J hits def-weil-derived-limit, def-weil-pbc-adic-derived-inverse-limit and lem-weil-pbc-pseudocoherent-normalized-algebra-tower were inspected as search candidates: the first defines the object and points to this helper; the other statements concern specialized adic constructions rather than arbitrary morphisms of two fixed Roos triangles. No candidate is cited for a theorem it does not state.

## Review by ND

I read derived.tex, remark-functoriality-derived-limit (0H9J), including both product-map formulas and the final warning, and definition-triangulated-category (0145), including TR2's negative shifted first arrow and TR3's three commuting squares. The local blueprint definition of def-weil-derived-limit was open alongside them. There are no new-node statements or sources to review.

For step 1 I opened def-weil-category-product, def-weil-inverse-system, def-weil-tower-transition-endomorphism and def-weil-triangulated-category. The product node states the universal property, its uniqueness and the product morphism's projection formula. The inverse-system node gives precisely f'_n φ_{n+1}=φ_n f_n; the transition node gives the projection formula for s and the claimed naturality of 1-s. The triangulated-category node supplies additivity for subtracting morphisms. The step independently computes both sides after every target projection, then uses product uniqueness; it does not appeal to an unstated exactness or preservation-of-products theorem. Both particular products are hypotheses of the item; no category-wide products or small-limit existence result is assumed.

For step 2 I opened the same triangulated-category definition and checked its actual TR2 and TR3 clauses. TR2 gives exactly the two displayed rotations, including -p[1] and -p'[1]. Step 1 supplies the one square TR3 requires, with first and second vertical arrows both a. Substituting in the definition's TR3 yields cδ=δ'a and a[1](-p[1])=(-p'[1])c, with c on shifted limit objects. This is a direct substitution into an axiom explicitly stated by the cited definition, not a use of a theorem about triangulated categories for which only a bare name was cited.

For step 3 I checked that the cited definition calls [1] an additive automorphism (equivalently here an additive autoequivalence). Its full faithfulness permits lifting c to φ and reflecting the equation after shifting. Cancelling both negative signs yields the requested first square, and cδ=δ'a yields the last square without changing either connecting morphism. These are elementary uses of inverse equivalences, additivity and preservation of composition, all written in the step. The existential TR3 axiom has no uniqueness conclusion; this matches the source's warning. No functorial choice of cones or of maps is claimed.

I checked small cases: zero towers give zero maps; a zero tower morphism admits the zero triangle morphism; the identity morphism of a tower with the identical chosen triangle admits the identity lift. For constant towers nothing in the proof requires nonzero 1-s, and no cancellation of 1-s or p is used. Thus uniqueness in special cases is consistent with the warning. There are no extra hypotheses of abelianness, enough injectives, exact products, or a model of the triangulated category. The positive-integer indexing is unchanged throughout.

B1-B8: no auxiliary node, partial proof disguised as a statement, duplicate, or unsearched Mathlib leaf was introduced. B9-B10: blueprint.same_as and the precise ancestor place are filled, and the exact Lean-attachment check was done. C1-C5: every ingredient is either the explicitly written product/shift calculation or an axiom/universal property in an opened cited definition, with verbatim quotations in citations.json. C6-C8: dependencies point to existing definitions, no reverse edge is added, and no off-route theorem is used. D1-D5: the original argument remains in the item, split into the product square, rotated TR3 and unshifted equations; nothing was moved to a restatement node. E1-E7: domains, signs, indices, products and all used hypotheses were checked above. My corrections were to the empty proof and missing blueprint search result, not to the mathematical statement. The second reader should particularly recheck the signed shifted square in steps 2-3.


## Second reading by ND

- Item: checked all hypotheses and both fixed connecting-map equations against derived.tex, Tag 0H9J, remark-functoriality-derived-limit, and Tag 08TC; agrees with the levelwise case m(n)=n, including the warning that uniqueness is not guaranteed.
- Step 1: opened the product, inverse-system, transition-endomorphism and triangulated-category nodes; their statements give the projection formula, tower compatibility and additivity used in every displayed equality. The projection calculation and product uniqueness are elementary; pass.
- Step 2: checked the actual TR2 and TR3 clauses against derived.tex, Tag 0145, definition-triangulated-category; the rotated third arrows are -p[1] and -p′[1], the square has vertical maps a,a, and both equations for c have the correct domains and signs. Direct substitution into the cited defining axioms is elementary; pass.
- Step 3: checked the shift autoequivalence and both equations from step 2; fullness lifts c, faithfulness reflects the composition equation, and cancelling the two negatives gives precisely p′φ=ap. The other square retains δ and δ′ without a sign change; pass.
- New nodes: none; no redundant elementary node, duplicate, Mathlib leaf or restatement was introduced. The read Mathlib declaration complete_distinguished_triangle_morphism₁ at Pretriangulated.lean:189-201 needs the square proved in step 1 and is not the whole tower statement.
- Edge cases: zero towers and the zero tower morphism admit zero lifts; the identical triangle and identity tower morphism admit the identity lift. No nonzero hypothesis, cancellation of 1-s, exactness of products, abelian structure or injectives are used. Indices remain n≥1, with f_n:K_{n+1}→K_n.
- Citations: independently compared all six citation records against the opened DAG statements; every quote is verbatim and every cited statement supplies the fact used. No new reverse dependency or off-route theorem is added.

Changes: appended this independent reading only; the mathematics, node fields and citations were already correct. The earlier attempted patch made no changes. The specified delivery command has a trailing dot unsupported by deliver.py; used its documented two-positional-argument syntax instead, without changing the tool.
