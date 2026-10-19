# Stage-1 report: lem-coef-presentable-right-adjoint-accessible

## Files written

- `dag/nodes/sec-six-functors/lem-coef-presentable-right-adjoint-accessible.json`: five-step split, unchanged statement, no Mathlib match.
- `citations.json`: nine entries, one verbatim quotation for every node used by every proof step.
- `searches.jsonl`: actual msearch records, including two semantic phrasings and the unsuccessful auxiliary-draft searches.

No new nodes and no Mathlib leaves are delivered.

## Attachments

None. Searches for the exact item id and presentable/accessibility/adjunction notions in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no declaration of this coherent infinity-category theorem. The ordinary-category presentability code in `WeilConjectures/CategoryTheory/Sites/TransfinitePlusSheaf.lean` does not state it. The read-only upstream master is reference material only and supplies no attachment here.

## WANTED

WANTED: Lurie, *Higher Topos Theory*, https://www.math.ias.edu/~lurie/papers/HTT.pdf, Proposition 5.4.7.7 and proof, printed p. 451; also Proposition 5.1.3.2 (mapping-space colimit test), Proposition 5.4.2.9 (rank enlargement), and Definition 5.5.0.1 (presentability), for the item. This document was read online, not found archived under `literature/`; therefore the expanded proof is marked `proof_origin.by = agent` as required by the standing brief. No Stacks tag states this infinity-category result; an ordinary-category Stacks theorem is not substituted for it.

## What was wrong or corrected

The imported statement is correct and is unchanged. Its proof was empty. An initial sandbox draft merely applied a new general-adjoint accessibility statement; on self-review I removed that uncommitted draft node because it moved the actual argument out of the item (delivery-errors D1/D2). The final split instead contains the compact-generator calculation and the detection argument itself, using existing smaller lemmas. No statement dispute or source error was found. All imported source/creation and blueprint ancestry metadata is retained.

An early dry run found a search-log packaging error: the auxiliary-draft searches had genuinely run through msearch, but its second argument put their log in a sibling sandbox. The exact original records were copied into this item's search log. These searches remain as genuine research records; the auxiliary theorem is not delivered. The final proof needs no new search-dependent node. I read Mathlib `CategoryTheory/Presentable/Basic.lean:49–78,113–133`, `Adjunction.lean:33–93,119–128`, and `LocallyPresentable.lean:35–99`: they concern ordinary categories and set-valued Hom. In particular `Adjunction.isCardinalPresentable_leftAdjoint_obj` assumes accessibility of the right adjoint; it cannot prove the required infinity-category assertion.

## Unfinished work

None in the one-level split. Existing dependency nodes retain their own states. No Lean was written or compiled and nothing was pushed; the independent second reader must review and deliver.

## Not duplicates

No new node is delivered. I searched the whole DAG and blueprint using `blueprint_refs.py search` for right-adjoint accessibility and accessible infinity functors. The existing `lem-coef-compact-model-pr-duality` includes a fixed-rank adjoint/compactness criterion, but not the existence of a rank asserted here. `lem-coef-small-family-accessibility-rank` assumes accessibility of the functors and `lem-coef-small-right-adjoint-diagram-compact-model` already depends on this item, so neither can prove it. Ordinary accessible-functor rank nodes concern ordinary categories. The final proof reuses the common compactness rank node rather than duplicating a rank lemma.

## Review by Q38

I read delivery-errors B through E, the chapter and unit records, and the current main-20261015 blueprint ancestor's proof paragraph 2: the finite-coefficient derived adjunction before the inverse-limit calculation. This item is the foundational accessibility input reached through its presentable Cartesian-fibration infrastructure. No chapter or unit route changes. I read HTT Proposition 5.4.7.7 and its proof online. It chooses compact generators in the target of the right adjoint, bounds the compactness ranks of their left-adjoint images, and tests filtered colimits on those generators. The final item follows that argument and writes out the detection instead of appealing to the whole theorem.

Step 1 uses `def-coef-presentable-infinity-category` for accessibility, a small equivalent model of an essentially small generating subcategory, and compact filtered presentations of every object. The same definition explicitly says presentability includes all small colimits. The chosen left adjoint and its mapping-space equivalences are exactly the item's adjoint hypothesis, not an additional existence claim. The object family is indexed by the vertices of a genuinely small quasicategory, so it is a U-small family.

Step 2 applies `lem-coef-infinity-common-compactness-rank` only to that small family of images under L in the accessible category D. I opened its statement: it asserts a common infinite regular cardinal in U making those objects compact, exactly what is used. Taking the maximum with kappa is legitimate because two cardinals are comparable and their maximum is one of the regular cardinals. Compactness is monotone here directly: every rho-filtered index is theta-filtered and kappa-filtered. This uses only the definition cited in the step. The proof does not claim that an accessible category is accessible at every larger regular cardinal; presentability already ensures that all the required colimits exist.

Step 3 uses the definition's precise mapping-space meaning of compactness twice, and the assumed adjunction between the two comparisons. The rank rho is fixed before choosing I or T. C and D both have the selected colimits. I verified that q goes from the colimit of R T to R of the colimit, and that the composite on mapping spaces is postcomposition by q: on the ith cocone component naturality of adjunction makes it postcomposition by R(t_i), which equals q s_i with its coherences. Thus a chain of abstract equivalences has not silently replaced the actual comparison. All spaces are taken in one common containing universe as in the compactness definition.

Step 4 uses three actual statements I opened. `lem-coef-infinity-mapping-composition` supplies associative/unital composition and inverse edges, so mapping out of an equivalent generator transfers the generator test. `lem-coef-infinity-yoneda-presheaf-limits` explicitly says that a colimiting cocone is tested by the natural equivalence from mapping out of its vertex to the limit of the contravariant mapping-space diagram. This is applied to a U-small filtered presentation of an arbitrary object; it is not a large-category colimit. Its naturality is part of that statement, so it identifies the actual map induced by q. `lem-cbc-enhanced-functor-cone-calculus` explicitly says objectwise equivalences of coherent transformations are equivalences. Applying the limit functor to a transformation and its inverse then gives inverse limit maps. Hence the test extends to every object. This cone-calculus node is a generic off-unit tool, declared only in `split_report.tool_uses`; no unit-level geometric argument is replaced.

Step 5 uses `lem-coef-infinity-mapping-composition` again for its exact homotopy-category equivalence criterion. Surjectivity on components at x = R y supplies v with q v = 1; injectivity at x = z gives v q = 1. This is the explicit two-sided inverse argument, not an uncited conservativity lemma. The cocone mapping-space criterion in `lem-cbc-enhanced-functor-cone-calculus` proves that replacing the colimit vertex z by the equivalent vertex R y preserves the universal cocone property. Since T was arbitrary, the same fixed rank proves the entire item. The elementary steps consist of choosing witnesses from definitions, the two compactness/adjunction comparisons, and the two inverse equations; the rank-existence and mapping-space limit theorems are cited non-elementary inputs.

For B1–B10, there are no new unsplit or leaf claims; all objects and notions in the unchanged statement have the same definition dependencies, TeX is singly escaped after JSON decoding, original blueprint fields are retained, and searches were actually run. For C1–C8, I compared each of the nine citations with the cited statement and supplied verbatim quotes; no proof of another node is used as if it were its statement. I traversed the cited nodes' dependency closures and found no path back to the item. The final server checks provide the authoritative cycle/route check. For D1–D5, the discarded generalization is absent and the final five steps carry the proof, with no hidden induction or omitted generator-detection argument. For E1–E7, source/target variance, smallness, regularity, compactness ranks and comparison-map naturality are checked above; no coefficient category or target statement is changed and no SGA source is used.

Small-case checks: if both categories are terminal the unique comparison is an equivalence. Identity adjunctions give the identity colimit comparison. For the ordinary-set example viewed in infinity categories, the countable-power right adjoint to product with a countable set need not preserve ordinary filtered colimits, so the proof correctly chooses a larger rank depending on L's generator images instead of reusing the source generator rank. An empty presentable category cannot arise because the empty colimit would supply an object. Even a vacuous generator family would cause no smallness failure: the common-rank node allows the empty small family, and the presentation/mapping-space test still has its empty limit interpretation. These checks introduce no extra theorem or hypothesis.

## Second reading by Q38

- Item statement: checked against HTT Proposition 5.4.7.7 (printed p. 451), with the presentable and coherent-functor meanings supplied by the cited definition nodes; all hypotheses and the conclusion are retained.
- Step 1: checked against the accessibility and compact-presentation clauses of `def-coef-presentable-infinity-category`; the small representative quasicategory and the left-adjoint mapping equivalence are exactly available.
- Step 2: checked against `lem-coef-infinity-common-compactness-rank` and the compactness definition; the maximum of the two regular cardinals is valid and filteredness/compactness are used monotonically.
- Step 3: checked against the compactness definition and the adjunction in the item; the comparison is (q:z\to R y), and naturality identifies the displayed composite with postcomposition by (q).
- Step 4: checked against the statements of `lem-coef-infinity-mapping-composition`, `lem-coef-infinity-yoneda-presheaf-limits`, and `lem-cbc-enhanced-functor-cone-calculus`; the presentation index is small and pointwise equivalences induce the required limit equivalence.
- Step 5: checked against the component and inverse-edge clauses of `lem-coef-infinity-mapping-composition` and the cocone criterion in `lem-cbc-enhanced-functor-cone-calculus`; the two equations (qv=1) and (vq=1) are obtained with the correct composition order.
- New nodes: none; therefore B1–B7, source checks, Mathlib-leaf checks, and duplicate checks were rechecked as in the existing review, with no new node to repair.

No files required mathematical correction. I appended this second-reading record only; the node statement, five proof steps, citations, and search records remain unchanged. The HTT PDF was read directly because no archived Stacks tag states this infinity-categorical result, and no SGA source is used.
