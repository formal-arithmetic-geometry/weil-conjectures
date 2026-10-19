# lem-coef-graph-product-model — Q74

## Files written

- dag/nodes/sec-six-functors/lem-coef-graph-product-model.json: statement, split; no exact Mathlib match. Eleven proof steps reuse seven existing nodes. The statement and its statement dependencies are unchanged.
- citations.json: exact statement excerpts for every step/node citation.
- searches.jsonl: searches made with the required msearch command; results inspected. The inherited search records remain in the item; the new records are appended verbatim with verdicts.

No new nodes and no new Mathlib leaves. No unit record needs realization: this is a subordinate created lemma, not its unit's key statement. All edits are confined to the assigned sandbox. No Lean was written, no compiler was invoked, and no git command was run in the shared repository.

## Attachments

None. Searched WeilConjectures in the read-only slopmaster2 checkout for the exact blueprint tag, graphProduct/graph_product/GraphProduct, coordinatewise, product model structure, and model-category references. The relevant coordinatewise hits are unrelated tensor/affine/linear-algebra calculations. No project declaration supplies the graph-model statement. In particular a general Mathlib model-category constructor would not be an attachment.

## Wanted sources

WANTED: Fernando Muro, Homotopy theory of nonsymmetric operads, Algebraic & Geometric Topology 11 (2011), Remarks 10.2 (printed p. 1596, PDF page 56) and 2.3 (printed p. 1546, PDF page 6), for lem-coef-graph-product-model. The publisher's PDF was read online at https://msp.org/agt/2011/11-3/agt-v11-n3-p13-p.pdf; it is not archived in literature/. No document was downloaded. Accordingly proof_origin.by is agent, with the current blueprint proof as the ancestry document, rather than falsely claiming an archived human-written proof.

## Findings and changes

The imported item had a statement and prior searches but no proof. It is true as stated. Remark 10.2 supports the product construction; Remark 2.3 describes insertion in one coordinate. The paper mentions right properness there. I did not read this as a claim about left properness: the latter is proved directly from the left-proper projective-chain node and the explicit coordinate pushout formula.

“Initial map in all other coordinates” means the map between the two initial objects, 1_0:0→0; Step 6 spells this out. It does not mean that a nonzero generator codomain is present in every other coordinate. Neither interpretation nor any target hypothesis has been changed.

Blueprint searches: ran blueprint_refs ancestor on the item and searches for “product model”, “locally presentable”, “graph”, and “model”; also searched the whole DAG for product models, discrete categories/presheaf presentability, small object arguments, cofibrant generation, and Muro. No blueprint statement duplicates this full assertion. Existing generic presentability/cardinal/cellular nodes are reused. The historical ancestry remains prop-coef-integral-exceptional-adjoint; I read both its master text and its main-20261015 statement and separate .proof.md under sk-thm-sf-package. The relevant place is paragraph 2, coherent finite-level adjunctions before the derived limit; the graph construction is infrastructure through the inherited dg free-model chain. No chapter or unit route is replaced and no SGA source is used.

Mathlib searches with two natural-language formulations found ModelCategory.mk', model axioms, Pi-category infrastructure, and stability of fibrations under products in one model category. I opened ModelCategory/Basic.lean:47-75 and Instances.lean:115-170: these do not construct the product-category model with the single-coordinate generators, local presentability, left properness, and tractability. The repeated query used a different discrete-functor formulation before concluding no match. The specialized presheaf theorem that is available is already the existing Mathlib leaf lem-coef-presheaf-local-presentability, so it is cited rather than recreated.

## Unfinished work

None in the one-level split. The projective-chain model inputs remain the existing cited nodes, with their original status. This delivery creates no further obligations as new nodes.

## Review by Q74

I read delivery-errors B through E in full, the item's source, the chapter/unit records, both versions of its blueprint ancestor, and the complete statement of each of the seven cited nodes. I checked the publisher's Muro Remarks 2.3 and 10.2 online and read the relevant local Mathlib presentability and small-object sources. The item has no blueprint_update field and the historical statement was retained.

Step 1 cites lem-coef-projective-cochain-monoidal-model for the combinatorial chain model and lem-coef-combinatorial-localization-presentability only for its explicit model-category conventions, which include completeness, cocompleteness and functorial generated weak factorization systems. No localization conclusion or mapping-space result is borrowed from the latter. The ring is exactly an arbitrary commutative R, so no field, Noetherian or finite-dimensional hypothesis has entered.

Step 2 uses the limit/colimit existence established in Step 1 and proves the product universal properties by identifying families of cones. It requires no extra theorem about functor categories. The product Hom is small because its index and factors lie in the fixed universe. Empty diagrams are included.

Step 3 cites lem-coef-presheaf-local-presentability. Its statement applies to an arbitrary small ordinary C and locally presentable A with small Hom and pullbacks. Here C is the discrete category on S×S, and A is the same chain category as Step 1, with pullbacks supplied by completeness. Both the family-to-functor identification and its inverse on maps are written explicitly; no equivalence-invariance theorem is used as an unexplained comparison. The cited statement actually supplies this general target-valued presheaf assertion, not merely Set-valued presentability.

Steps 4 and 5 use only the model axioms already obtained in Step 1. I checked that each lift and each functorial middle-object map is a family indexed by T, with no morphisms imposing compatibility between coordinates. Retract closure and two-out-of-three are component equations. The factor-and-lift retract test establishes the actual weak factorization systems, rather than only the existence of two unrelated factorizations.

Step 6 cites lem-coef-projective-cochain-monoidal-model for its explicit I and J, with cochain indexing S^{n+1}→D^n. The source and target at every other coordinate are both zero. The Hom bijection is a direct tuple calculation, and its compatibility with composition is component evaluation. These are sets because S×S and the integers are small.

Step 7 cites that same node for the statement that I and J are generating sets. I verified that lifting squares and fillers are in bijection with the corresponding single-coordinate squares. Therefore the right classes are precisely trivial fibrations and fibrations; cofibrations are obtained using the already established lifting systems of Step 5. There is no citation to a graph-model theorem that would merely restate our item.

Step 8 cites lem-coef-object-presentability-rank for every generating domain in the graph category, after its local presentability is established, and lem-coef-small-family-regular-bound for the tagged union of the rank-sized sets. I read LocallyPresentable.lean:93-105 and HasCardinalLT.lean:201-206. The statements provide ranks in the same universe and a strict common regular bound. The injection of each fibre into the tagged union is written out. This uses only a small family, including when the family is empty.

Step 9 cites lem-coef-small-object-cell-factorization. I read its statement and SmallObject/IsCardinalForSmallObjectArgument.lean:76-88,318-330,412,460-469,508-515. The cardinal preservation condition required there is weaker than what Step 8 supplies after the displayed regular-ordinal argument: fewer than tau_k objects, each below lambda, have a supremum below lambda. Its factorization, cellular first leg, right lifting class, and retract characterization are all expressly in the cited statement. Small Hom sets and small colimits were checked in Step 2, so there is no large category of lifting squares or unsupported small-object invocation. This establishes conventional cellular cofibrant generation as well as generation of the lifting classes.

Step 10 cites the cochain-model node for the dg-projective cokernel criterion and standard generators. Hom from a sphere into an acyclic complex is just a shift, so its acyclicity follows by the degreewise kernel/image test. Composing the two lifting fillers proves cofibrancy of D^n, and zero is cofibrant by its identity map. Thus both I and J, and their single-coordinate images, have cofibrant sources and targets. The citation of lem-coef-projective-chains-monoidal-model is for its written tractability convention; I did not assume that its proof, rather than its statement, grants extra source properties.

Step 11 cites lem-coef-projective-chains-monoidal-model for its explicit left-properness statement. The hypothesis on the pushout leg is a cofibration in every coordinate and the other leg is a quasi-isomorphism in every coordinate, so each application has exactly the required hypotheses. The universal-property formula in Step 2 identifies precisely the resulting graph pushout map. Tractability follows from the local presentability, generated systems and cofibrant generators proved above, with no global cofibrancy assertion about arbitrary chain complexes.

For the edge cases I checked S=empty (the category is terminal, both sets of generators are empty, and its sole map has both lifting properties), a singleton S (all constructions return the original chain model), and infinite small S (only small products/families are used; no finite-support restriction is imposed on graphs). The zero ring also causes no exception: all displayed generators and tests remain meaningful. I corrected no statement, and introduced no new node that could be elementary, a duplicate, a Mathlib theorem, or a restated clause of the item. Every non-elementary input has a cited node whose statement contains the verbatim excerpt in citations.json. Every proof step has fewer than 2000 characters; no long hidden comparison is left in a step.
