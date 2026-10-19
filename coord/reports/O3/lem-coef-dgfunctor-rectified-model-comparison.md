# Stage-1 worker report

Item: lem-coef-dgfunctor-rectified-model-comparison. Group: N3. Date: 2026-10-17. Direct delivery; no second worker was started.

## Files written

- dag/nodes/sec-six-functors/lem-coef-dgfunctor-rectified-model-comparison.json: statement, split; no Mathlib match. Six proof steps replace the empty proof. The statement and all inherited provenance/search records are retained.
- citations.json: eleven entries, one for each node used by each proof step, with verbatim excerpts of the cited statements.
- report.md: this report. searches.jsonl records five searches executed through the required msearch.py command. write_split.py is sandbox-only preparation, not a delivered DAG node.

New nodes: 0. Mathlib leaves: 0. The proof depends on the existing dg model structure, dg-enrichment rectification, enriched-category tensor calculus, and localization-homotopy-category nodes. No unit record is changed: this item is a descendant of a blueprint node, not the unit's key node.

## Attachments

None. The searches of WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 for the exact item id, rectified/dg-functor terminology, and quasi-functor terminology found no declaration stating this item. The upstream master source was also searched read-only; it supplies no finished-proof evidence.

## WANTED

WANTED: Rune Haugseng, Rectification of enriched infinity-categories, arXiv:1312.3881v4, Theorem 5.8 and Example 5.11, for lem-coef-dgfunctor-rectified-model-comparison. Read at https://arxiv.org/html/1312.3881v4; not archived in literature/.

WANTED: Rune Haugseng, On the tensor product of enriched infinity-categories, arXiv:2311.13362v1, Corollaries 9.3-9.4 and Remark 9.5, for lem-coef-dgfunctor-rectified-model-comparison. Read at https://arxiv.org/html/2311.13362v1; not archived in literature/.

WANTED: Denis-Charles Cisinski, Higher Categories and Homotopical Algebra, Theorem 1.6.6, Corollary 1.6.8 and Remarks 7.1.4 and 7.1.6, printed pp. 24-25 and 324-325, for lem-coef-dgfunctor-rectified-model-comparison. Read at https://cisinski.app.uni-regensburg.de/CatLR.pdf; not archived in literature/.

These are foundational dg/infinity-category results; there is no Stacks tag stating them. No SGA source was used. No literature was downloaded or written. The proof is marked agent-written because its representing-object specialization is written here and its external sources are not archived.

## Audit findings and corrections

The input had no proof. There is no statement dispute or change of hypotheses. In particular, the tensor comparison is the item's explicit assumption, not a conclusion silently extracted from non-monoidal rectification. The representing bijections are set-valued. The proof does not assert that arbitrary such families lift to a specified coherent family of bijections, or that a space of lifts is contractible. Instead it constructs one isomorphism in Hqe by naturality and uses equivalence detection in the enhanced localization. This gives the claimed enhanced equivalence and the requested single evaluation homotopy.

The blueprint ancestry is prop-coef-integral-exceptional-adjoint, proof paragraph 2 (the mapping-complex adjunction and its specified units/counits before inverse limit). I read that blueprint file and the chapter/unit records. This comparison is below that route, and does not replace its coefficient or duality argument. The item has no blueprint_update field. The complete blueprint searches for rectification, internal Hom and representing objects found no blueprint node stating this comparison. In particular, lem-pc-representable-unique and det-sp-representing-pair-uniqueness concern schemes and smooth-purity representing pairs; neither states the dg rectification assertion.

I reused lem-coef-localization-homotopy-category instead of creating a new lemma for lifting an isomorphism from the homotopy category. The uniqueness calculation is elementary and is written out in step 4 instead of creating a node. All four cited nodes are in the same unit. Their transitive statement/proof dependencies do not reach the item.

## Mathlib searches

Five actual msearch.py queries are retained in searches.jsonl and added to the item's inherited mathlib_searches: LeanFinder with two distinct phrasings, LeanSearch, Loogle for CategoryTheory.Enriched.FunctorCategory.homEquiv, and grep for rectification/dg-category/quasi-equivalence terminology in Mathlib/CategoryTheory. All five services/commands returned successfully. I read the returned signatures and the source of Mathlib/CategoryTheory/Enriched/FunctorCategory.lean (ordinary enriched ends and homEquiv) and Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean (ordinary ihom evaluation). These do not state dg rectification, an enhanced localization equivalence, or this comparison. The Tor hits concern derived functors on objects of an abelian category. No result was declared unavailable or a leaf incorrectly. The original item's searches are retained as inherited evidence, not claimed as newly executed N3 searches.

## Not duplicates

No new nodes were created; no new/existing-node pairs require a duplicate justification. The comparison is proved directly rather than restated in a new child. The two basic supporting assertions already exist as rectification and localization nodes, and the closed tensor calculus is also reused.

## Review by N3

I read the item, the full statements of all four cited nodes, the ancestor blueprint proof, and the chapter/unit records. I read Haugseng Theorem 5.8 and Example 5.11: the unbounded chain-complex specialization over a commutative ring is explicitly covered, so setting the ring to Z gives the existing rectification interface. I read Remark 9.5 of the later tensor paper: its closed enriched tensor gives the internal Hom, with a complete target ensuring the internal Hom is a category. I read Cisinski Theorem 1.6.6, Corollary 1.6.8 and Remark 7.1.6: these provide homotopy classes, inversion detection, and the ordinary localization comparison. These assertions are used through existing nodes, not through uncited external black boxes. No new node needs a separate source audit.

Step 1 uses lem-coef-localization-homotopy-category for hL = Hqe, not just for the definition of a homotopy category. The category and its wide class of quasi-equivalences satisfy that node's hypothesis by the definition of the enhanced localization. I checked the size hypothesis: the category of small dg categories fits in a further universe, and the final sentence of lem-coef-dgcat-model-structure explicitly preserves mapping spaces and morphism sets for the original objects after enlargement. Thus the use of all small test categories is legitimate. Naturality across an inverse follows simply by inverting the two bijections in its commuting square.

Step 2 uses the equivalence of infinity categories in lem-coef-dg-enrichment-rectification, whose essential surjectivity supplies a small dg model with a chosen comparison rho. The tensor-calculus node explicitly works with small enriched categories in fixed nested universes and supplies their internal Hom. This is neither a model for a large unrestricted functor category nor a Morita localization.

Step 3 takes full faithfulness of that same rectification equivalence, the internal-Hom adjunction from the tensor-calculus node, and the tensor identification explicitly assumed by the item. Taking connected components uses the hL identification already proved in step 1. The comparison beta is natural because these are natural adjunction and functor equivalences. Its formula uses evaluation after rho and tensoring with the identity; it fixes the evaluation convention needed in step 6.

Step 4 is elementary: evaluating gamma = beta inverse composed with alpha on identities defines e0 and f0. Naturality gives gamma(u) = e0 composed with u and the inverse formula. Substituting f0 and e0 proves both inverse identities, so there is no appeal to an unprovided general Yoneda theorem. This calculation is strictly below the whole dg comparison and is not a separate node.

Step 5 cites the exact equivalence-detection sentence of the localization node. Every homotopy-category arrow has a representative edge by its stated definition; invertibility of e0 makes any such representative an equivalence. The rectification node explicitly defines enriched equivalences to be fully faithful and essentially surjective, hence it identifies entire D(Z)-valued mapping objects. It would be incorrect to deduce this directly from equality of degree-zero Hom sets; the proof instead first constructs the enhanced equivalence.

Step 6 uses the tensor-calculus statement's coherent composition/evaluation/currying and the already established full faithfulness of rectification. The identity alpha_R0(1) = beta_R0(e0) is proved by step 4, and step 3 writes its coherent evaluation representative explicitly. Equality of these classes is homotopy of arrows in L by the homotopy-class description in the localization node. This proves precisely one evaluation compatibility homotopy and makes no stronger claim about coherent lifting of every parameter family.

For edge cases I checked J empty (its tensor input is empty and its internal Hom is the terminal enriched category); B empty with J nonempty (both representing functors are represented by the empty dg category); and J the tensor unit (the comparison reduces to ordinary representing-object uniqueness for B). None of the steps chooses an object of an empty category, assumes nonemptiness of J or B, or assumes flatness of the original dg categories. Smallness, unbounded complexes, quasi-equivalence rather than Morita equivalence, and the assumed tensor agreement are retained throughout. All six steps are shorter than 2000 characters; no long inline standard lemma is hidden. citations.json was checked against the actual node statements before writing. This review addresses B1-B10, C1-C8, D1-D5 and E1-E7: no new statement-only nodes, missing definition nodes, duplicate children, uncited non-elementary comparisons, cycles, off-unit tools, restated clauses, or extra hypotheses were introduced.

## Unfinished work

No mathematical part of this one-level split remains. The four pre-existing foundational nodes keep their existing status and are not split or edited by this delivery. Validation and push are performed by the required delivery tool.
