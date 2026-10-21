# Worker report

Item: lem-sf-cbc-word-reconstruction-coherence. Group: Q13. Stage 1 only. 2026-10-21.

## Files written

- `dag/nodes/sec-smooth-purity/lem-sf-cbc-word-reconstruction-coherence.json`: statement, split; eight explicit proof steps; not a Mathlib leaf. The statement and its statement dependencies are unchanged. All inherited fields and six earlier search records are retained; six genuinely run searches from this sandbox are appended.
- `citations.json`: a verbatim statement quotation for every step/node pair (nine pairs).
- `report.md`: this report. `searches.jsonl` is the search command's own log; `write_split.py` is the sandbox-only JSON writer.

There are **0 new nodes and 0 new Mathlib leaves**. The proof cites the existing category definition/Mathlib leaf and the existing whiskering-exchange Mathlib leaf. No unit file is changed: this item is a categorical prerequisite, not the unit's key statement.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and id, reconstruction/coherence terminology, word comparison terminology, and the geometric parent's `SfCbcWord`, `SfCbcExpression` and theorem name. No project declaration states this item. The parent's declaration recorded under `lean/Sheaf/` is not an eligible attachment to a project declaration under `WeilConjectures/`, and its supplied generic categorical prerequisite is the present item, not a finished proof to reuse.

## WANTED

None. The argument is written by this worker; it is not attributed to a missing reference.

## What needed repair

The item was statement-only, with no proof. Its statement is true as written; no STATEMENT-DISPUTED correction is needed. I supplied the full recursion/naturality/uniqueness argument and both independent finite inductions instead of introducing new nodes for its own clauses. The source remains the imported source, while `proof_origin` and each proof step point to the current main-20261015 `fix-lem-exchanges.proof.md`, Step 5, and explicitly mark the component proof as agent-written. The current blueprint moves this unit from the historical smooth-purity directory to six-functors-basics; I followed the current text while preserving the item's fixed chapter and source fields.

## What remains unfinished

Nothing in the stage-1 mathematical split. This delivery provides a natural-language proof, not Lean code. No compiler, Lake, build, or repository git command was run.

## Searches and not duplicates

The six searches logged in this sandbox use LeanFinder twice (distinct phrasings), LeanSearch, Loogle, and two Mathlib grep queries. The services answered successfully. I read the actual types of the hits, especially `Paths.liftNatTrans` and `Paths.liftNatIso` in `Mathlib/CategoryTheory/PathCategory/MorphismProperty.lean:66,78`; these extend naturality for vertex components into one fixed category. They do not give edge-indexed comparison transformations between distinct functor composites, their recursive uniqueness and all binary-expression identities, or the additional reconstruction unit. A construction turning this into an appropriate higher-category universal property would itself be a proof, not a one-line specialization. I also read the associator and unitors at `CategoryTheory/Functor/Category.lean:166,174,185`, and the exchange law at `CategoryTheory/Whiskering.lean:203`. The latter is already an existing DAG leaf, so I cite it.

I ran whole-blueprint searches for natural transformation, parenthesization, reconstruction, word, and coherent word, and searched the whole DAG for these concepts and relevant formulas. I read the statements of `lem-sf-kunneth-coherence`, `lem-pur-finite-expression-reduction-comparison` and `lem-pur-expression-counit-substitution-coherence`: they concern respectively geometric Kunneth comparisons, semilinear derived-system effectivity, and counit-normalized tensor/pullback substitution. None states this generic arbitrary-category unary-word result with the given unit, or specializes to it. The geometric parent `lem-sf-cbc-compact-support-composition-limit` uses this item and cannot be cited back. I read its use of the word lemma, its blueprint ancestry and its review; no geometric conclusion is imported into this proof.

## Not duplicates

No new nodes were created, so there are no new/existing node pairs or same-tag collisions to justify. The existing whiskering-exchange leaf is reused, not restated as a new node.

## Review by Q13

I read the chapter and unit records, the three-level route rule of SETUP.md, GOAL.md, the stage-1 contract, and both copies of delivery-errors.md B through E. For the item's source I read the historical `fix-lem-exchanges.md` and the current `main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/fix-lem-exchanges.proof.md`, especially Step 5's composition compatibility. This proof supplies only the abstract word calculation requested by the already-reviewed geometric parent; it assumes its generator comparisons and does not claim to construct geometric exchanges. There is no new node needing another source. I read both cited node files in full. For the category laws I checked Stacks Tag 0014, `categories.tex`, `definition-category`; for the exchange leaf I checked the exact Mathlib statement at Whiskering.lean:203-207. No SGA route is used.

Step 1 uses only the identities and associativity in `def-nagata-category` and the inline functor definition: evaluating a composite on objects and morphisms gives identical expressions, so the actual associators and unitors have identity components. This explicitly constructs and compares the canonical flattenings; it does not invoke an unproved general bicategorical coherence theorem. I checked the Mathlib associator/unitor definitions against that assertion. Whiskering these maps still has identity components because functors preserve identities.

Step 2 cites the same category laws. I checked both displayed substitutions: first naturality of the already-constructed q_W at u under G_e, then naturality of the supplied q_e at F_W(u). All endpoints match: the result lies in T_v, starting at R_v F_e F_W(x). The empty transformation is natural, and the induction decreases the number of edges. Thus no implicit theorem about whole functor categories or a large colimit is being used.

Step 3 uses the identity laws from the category node, and identity preservation from the statement. It verifies that the empty-word recursion gives the specified singleton map and proves uniqueness by actual length induction. The family is determined by the recursion itself, not by a faithfulness assumption.

Step 4 uses the category laws for the two inverse equations. Its only closure hypothesis is exactly the given F_e(E_t) subset E_v. At the induction step this applies to F_W(x), which the induction has already put in E_t. The component q_e is therefore invertible at precisely the objects where the statement promises it. The displayed inverse uses the functor image of the inverse of q_W; composing in either order gives the appropriate identity. Multiplying the naturality square by inverses verifies inverse naturality on the full subcategory, rather than merely asserting that pointwise invertibility is a natural isomorphism.

Step 5 again uses the category laws. I checked the naturality equation before restriction: naturality of q_W survives applying L_t by preservation of compositions, and naturality of eta_t is applied at F_W(u). Only for invertibility do I restrict to E_s, where Step 4 ensures eta_t(F_Wx) is invertible. I checked the order of the two factors in the inverse and the empty-word identity a=eta. No adjunction of L and R is assumed or needed.

Step 6 uses category associativity and the functor law. Its induction fixes W and varies the length of V. The empty case is written, and in the successor case the displayed middle expression is exactly G_e applied to the induction hypothesis, followed by q_e at F_V F_W(x). The final two factors are the recursion for q_eV evaluated at F_W(x). Consequently the proof establishes concatenation before calling on arbitrary expressions; it is not circular.

Step 7 uses those same laws together with the already-proved Step 6. Its induction is on expression trees, with both edge and empty leaves as base cases. At a binary vertex the two child hypotheses identify the actual q components and the actual functor images, so the recursive composite is precisely the concatenation formula. Both children have smaller trees even if their flattened words are empty. This covers empty factors inserted inside arbitrary nests. The flattening is restored at the end using Step 1's actual identity components; equality is direct equality of families, not reflection of equality along R or L.

Step 8 cites `lem-amb-natural-transformation-whisker-exchange` in addition to the category laws. Its statement literally gives the displayed equation for c_E and eta_t after the six substitutions written in the proof. I verified its domain category D_s, middle category D_t and target category D_t, and that the transformations are natural on the whole source. Applying L_t to Step 7's equation and using this exchange gives the reconstructed equation in two displayed equalities. Both equalities therefore hold on all D_s even though the invertibility assertions require E_s.

I tested the empty index set (all claims vacuous), no edges (only empty words), empty categories/subcategories, a singleton word (the prescribed q_e), and a three-edge word: both bracketings evaluate to G_3 G_2(q_1) followed by G_3(q_2 F_1) followed by q_3 F_2 F_1. Arbitrary finite trees of empty factors reduce to identity components and a=eta. For a singleton index and identity R,L,eta, the formulas reduce to the ordinary composite of generator natural transformations; this tests the order of composition. I also checked that nothing requires q_e or eta invertible outside E, or requires R/L faithful. Every proof step is below 1000 characters, so none crosses the 2000-character long-step threshold. The small identity, inverse, and naturality calculations are kept as elementary steps rather than new lemma nodes; the two substantive word/expression inductions and the recursive construction are marked non-elementary and written out completely.

The citations file contains verbatim substrings of the current statements, one for every cited node in every step. There are no unsupported tag-only citations, new statement-only nodes, off-route non-Mathlib tools, or cyclic dependencies. Statement and hypotheses are unchanged.
