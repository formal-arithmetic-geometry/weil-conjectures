# Q32 stage-1 delivery: lem-coef-scat-fixed-object-pushout-comparison

## Files written

- `dag/nodes/sec-six-functors/lem-coef-scat-fixed-object-pushout-comparison.json`: existing statement node, now split into five explicit proof steps. Statement unchanged. Reuses the existing simplicial-category, free-arrow-adjunction and colimit-definition nodes. No Mathlib match.
- `citations.json`: verbatim statement excerpts for every node used by every proof step (with additional adjunction-naturality excerpts).
- `searches.jsonl`: actual Q32 msearch query records. The item's inherited Q07 searches are retained; Q32's executed searches are appended to the node, including the invalid Loogle namespace and its corrected search.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean files, units, chapter records, source checkouts or shared-repository files were written.

## Attachments

None. Searched the entire project `WeilConjectures/` tree in the read-only slopmaster2 checkout for the exact blueprint tag and for fixed-object/free-arrow/simplicial-category terminology. No declaration states this item. The upstream master checkout is reference material only; it supplies no attachment claim.

## Literature / wanted

WANTED: Julia E. Bergner, *A model category structure on the category of simplicial categories*, arXiv:math/0406507, Section 1 and Lemma 3.4 (horn case, printed p.11), for lem-coef-scat-fixed-object-pushout-comparison; the PDF is not archived under literature/ on this machine. Read the online PDF at https://arxiv.org/pdf/math/0406507 (16 pages), particularly the definitions on printed pp.1-3 and the fixed-object comparison on printed p.11. No download or literature edit was made.

The proof is marked `proof_origin.by = agent`. Bergner motivates the horn comparison but does not give this full arbitrary-map, repeated-endpoint, prescribed-object-function statement. The explicit target reindexing and universal-property proof here is the agent's argument, not a claim that the source contains all these clauses. No Stacks tag states this strict enriched comparison; no invented tag is attached.

## What needed correction

The imported item had no proof. Its stated mathematical assertion is correct; no STATEMENT-DISPUTED correction or weakening was needed. Added the existing `def-weil-pbc-category-colimit` as a statement dependency because the statement uses pushouts. The original statement, source, creation stamp and blueprint ancestry are retained.

The source's displayed horn comparison uses distinct labels and a relabelled complement. That presentation by itself does not address an attaching functor identifying the two endpoints. The delivered proof does: it works in a target category indexed by O, without identifying labels even when their images coincide. This is an expansion of the implicit comparison, not an assertion that Bergner's lemma is false.

Read the main-20261015 blueprint statement and proof of `prop-coef-integral-exceptional-adjoint`, its paragraph-2 adjunction calculation and naturality sentences, the current chapter and unit records, and the parent `lem-coef-simplicial-interval-cell-stability` step 3. The recorded ancestry is foundational support for that horn comparison. The item is not the unit's key statement; no unit realization changes are needed. There is no off-unit theorem tool: the only off-unit node is the existing colimit definition (already a Mathlib leaf).

## Not duplicates

No new nodes were created. Whole-DAG searches for fixed-object pushouts and the blueprint searches for `fixed-object pushout` and `free-arrow` found no blueprint equivalent. Read the nearby `lem-coef-scat-arrow-cell-word-filtration`, `lem-coef-scat-bergner-left-proper-pushouts`, and `lem-coef-sorted-simplicial-algebra-model`: the word-filtration statement assumes an injective attaching map, the left-properness statement is homotopical, and the sorted-algebra statement gives a fixed-object model structure. None replaces the arbitrary-map comparison proved here.

## What remains unfinished

Nothing in the mathematical split. The two existing theorem dependencies remain separately queued items; their proofs have not been copied, silently used, or split in this delivery. The required server dry run and direct push are performed after this report is written.

## Review by Q32

I read delivery-errors B through E with the item, both theorem dependency statements and the colimit-definition statement open. I checked the proof against the online Bergner source, rather than treating its phrase about working in the fixed-object category as the proof of the missing comparison. There are no new nodes whose sources or edge cases need separate checking.

Step 1 uses `lem-coef-simplicial-interval-lifting` for the meanings of U and sCat_O and the fixed-object model structure, hence its cocompleteness. It uses `lem-coef-fixed-object-free-arrow-adjunction` for the actual length-one word maps and their naturality. I checked that its statement includes the word construction, not just an abstract adjunction. Equal endpoints cause no problem: U has no composable pair of nonidentity arrows, so mapping its arrow to a loop imposes no extra relation. The cocone equality is checked on objects and on its unique nonidentity mapping set. `def-weil-pbc-category-colimit` supplies exactly the ordinary cocone universal property, specialized to the finite three-object span; no large indexing category is involved.

Step 2 uses only the explicit category/functor definitions in `lem-coef-simplicial-interval-lifting`. I wrote the mapping sets T_f(x,y)=T(fx,fy), its composition and its projection, then gave the inverse correspondence on mapping-set maps. The identity and composition equations are literally those in T. This is a short definitional step, not a hidden reindexing theorem. In particular f may identify any number of labels: T_f still has precisely the small set O as its objects, and all its mapping sets remain small.

Step 3 uses the adjunction node's actual naturality in both K and T, to identify the two composites from F(K) with ell i and G h. The quoted adjunction applies to T_f in sCat_O, not directly to the arbitrary-object target T. Its hypotheses hold for every small O and every a,b, explicitly including a=b. With equality of the two composites established, the colimit node gives the unique identity-on-O extension. I checked both inverse directions of the restriction bijection: restricting the constructed extension gives the input pair; any competing extension has the same object function because j is identity on O, and its whole free-L leg is determined by the adjunction, so fixed-object uniqueness applies. No claim about a homotopy pushout or mappingwise colimits is used.

Step 4 uses the precise U(K) definition in the interval node, including its identity and empty mapping sets, to identify arbitrary functors U(L)->T with the displayed target objects and arrow map. Equality on U(K) forces both endpoint objects, even if K is empty, since U(K) still has its two labelled objects. Thus the equation on the span is exactly the equation in the item's pairs. Applying the colimit-definition node now proves the variable-object pushout, not merely an isomorphic fixed-object span. The same node's uniqueness-up-to-unique-isomorphism clause supplies the canonical object-set identification for another pushout choice. The step is elementary because it only unpacks that definition and step 3.

Step 5 cites no new theorem. Postcomposition acts by (G,ell) -> (SG,S ell), and the square commutes by associativity of composition of the displayed maps. The inverse commutes by the uniqueness already proved in step 3. This establishes naturality for arbitrary target functors, including ones identifying objects, and maps the f-part to the (Ob S)f-part. It is not an appeal to an unspecified transport or coherence lemma.

I tested the small cases: a=b in a singleton O (the free category has all loop words, handled by the existing adjunction); K empty (only endpoint compatibility remains); L empty with an existing map K->L (K is empty too, so the attachment is trivial); i an identity (the pushout is C); a noninjective i (the compatibility can impose relations in C, which the pushout property permits); a noninjective f (distinct O labels remain distinct in T_f); and a target with no objects (there is no f because O contains a and b, so both sides are empty). No Kan or monomorphism assumption is used. O empty is excluded already by a,b in O, not by an added hypothesis.

For C4 I verified every quoted fragment against the cited node's statement and placed a quote for every step/node pair in citations.json. For C1 I checked that all non-elementary inputs are those cited statements; the remaining operations are explicit definitions and the universal property, with no normal-form theorem or preservation-of-colimits theorem hidden inline. For B and D there are no statement-only child nodes, duplicate nodes, or clauses moved elsewhere. For C6 I checked that the chosen colimit definition has no dependencies and both theorem nodes do not depend on this item; no parent stability theorem is cited. For E I checked the actual domain/codomain of every map and the equal-endpoint and empty-source cases above. All five proof steps are shorter than 1,200 characters, so none meets the 2,000-character long-step threshold; they also contain no source-described standard lemma requiring extraction.

The msearch results were read: the first semantic phrasing finds AttachCells/SmallObject and simplicial-set pushouts; the second finds SimplicialThickening and enrichment constructions. LeanSearch finds parametrized pushout-products and pointwise functor-category pushouts. These require an already established pushout square or concern different objects; none supplies this comparison in one line. The grep hits concern simplicial-set pushout-products. The first Loogle query had an unknown identifier; it is explicitly recorded as invalid, and the corrected CategoryTheory.IsPushout query returned no hits. The proof therefore remains a split node, not a claimed Mathlib leaf. No searches were fabricated and no compiler was run.
