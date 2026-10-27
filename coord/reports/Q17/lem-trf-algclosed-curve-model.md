# Q17: lem-trf-algclosed-curve-model

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-algclosed-curve-model.json`: statement, split into seven complete steps; no Mathlib match for the whole item.
- `citations.json`: one exact statement quotation for every use in every numbered step.
- `searches.jsonl`: actual Q17 search-command log. The item's inherited Q30 searches are preserved and distinguished by date; five fresh searches supplement them.
- `report.md`: this report.

There are **0 new nodes and 0 new Mathlib leaves**. The sandbox initially held only dispatcher brief markers, so there was no earlier split or report to overwrite.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag, curve models, proper/projective models, and function-field constructions. `IsCurve.exists_projectiveClosure` in `AlgebraicGeometry/Curve/Compactification.lean:88` starts with an already given integral curve; it does not construct one from an arbitrary field extension or state the valuation clause. The generic-model-field declarations concern finite covers of curves already given. No project declaration states the whole item under its hypotheses.

## Literature

No WANTED sources. I read Stacks `curves.tex`, Tags **0BY1** (`theorem-curves-rational-maps`, especially the final parenthetical compactify-then-normalize route) and **0BY3** (`lemma-nonsingular-model-smooth`); `varieties.tex`, Tag **0BXN** (`theorem-varieties-rational-maps`, last paragraph constructing a finite-type domain) and Tag **0A21** (`lemma-dimension-locally-algebraic`); `algebra.tex`, Tag **00P0** (`lemma-dimension-prime-polynomial-ring`); `morphisms.tex`, Tags **056B** (`lemma-scheme-theoretic-image-reduced`), **01WC** (`lemma-locally-projective-proper`), **035Q**, **035S**, and **0BX5** (`lemma-characterize-proper`). Tags were checked against `literature/stacks-project/tags/tags`.

I also read the actual statements and sources of the reused DAG nodes, the blueprint's affine compactification proof, and the current main-20261015 affine compactification statement. The imported item is a supporting node, with no `blueprint_update`; its inherited ancestry places it in the Temkin/nearby-cycle branch of `lem-trf-local-term-locality`. The proof realizes that curve-model input without modifying any chapter, unit or upstream target. No SGA source is used.

## Statement dispute and correction

**STATEMENT-DISPUTED:** The phrase “valuation ring B contained in E containing k”, interpreted using the cited abstract definition of valuation ring, does not ensure that the fraction field of B is E. Take E=k(t) and B=k. The field k is itself a valuation ring and is a subring of E containing k. A map Spec k to any finite-type k-curve selects a k-rational closed point, so its pullback along Spec E to Spec k cannot be the generic-point morphism. In particular this fails on the intended model P1. More intrinsically a factorization through Spec k would require a k-embedding k(C)=k(t) into k, which is impossible.

I made explicit the intended source condition `Frac(B)=E`, equivalently the valuation-subring property for every nonzero element of E. Stacks 0BX5 and the existing proper-valuative API both specify the fraction field. Under the usual convention that “valuation ring in E” already means a valuation subring of E this is a clarification; under the literal abstract-definition reading it repairs a false statement. The geometric conclusion and all its other hypotheses are preserved. No upstream target statement or definition was changed.

## Mathlib searches

The five Q17 searches in the node have exactly the tool/query pairs in `searches.jsonl`: two LeanFinder phrasings, one LeanSearch query, one Loogle pattern and one Mathlib grep. All five services returned successfully. The first LeanFinder result was recovered from its actual log; the other result sets were read from command output. I read the relevant local source: `Mathlib/NumberTheory/FunctionField.lean:57-74,99-138`, `Mathlib/AlgebraicGeometry/FunctionField.lean:31-100`, and the Weierstrass integral-model/reduction declarations. `FunctionField` and `functionField_iff` concern a finite-dimensional rational-function extension; `Scheme.functionField` and the stalk fraction-ring instance concern an already given integral scheme. Integral models of Weierstrass equations only handle elliptic equations. None constructs a proper smooth curve from an arbitrary one-variable field. Loogle and the projective-function-field grep returned no hits. The old searches are retained as historical material, not claimed as Q17 executions.

## Not duplicates

No new node is proposed. Whole-DAG keyword/tag searches and `tools/blueprint_refs.py search` for “function field”, “curve model”, “normalization”, “projective completion”, and “finitely generated field” located the existing tools used below. In particular I reused the affine compactification, normalization-properties, affine-fraction-field, and projective-proper nodes rather than introducing a normal-projective-model node. `lem-sfb-proper-curve-function-field-morphisms` covers full faithfulness of the curve/field correspondence, not existence, and is not cited for existence. There is no new/existing same-tag pair to justify.

## Review by Q17

I checked the proof against B through E of `coord/delivery-errors.md`, including both recorded versions, with the cited node statements and the Stacks passages open. Here is the mathematical check of every step.

1. The field generators give the concrete domain A=k[e1,...,er]. Its fraction field contains those field generators and lies in E, proving equality without assuming an algebraic model theorem. The finite-type algebra and scheme definitions give the polynomial presentation and finite-type structure map; the integral-scheme definition applies because A is a domain. I explicitly cite `lem-sc-integral-function-field-affine-fraction`, whose statement identifies the generic stalk with the fraction field of a nonempty affine open. This avoids using a definition of function field as a theorem about its stalk. The remaining localization at zero is written out. This is the elementary finite-generation argument in 0BXN, not a new lemma.

2. I opened `lem-weil-pbc-finite-type-domain-dimension-trdeg`: it assumes precisely a finite-type algebra over a field that is a domain, and identifies its Krull dimension with the fraction field's transcendence degree. A meets all three hypotheses from step 1. `def-weil-pbc-krull-dimension-ring` explicitly states agreement with the dimension of Spec A, so the transition to topological dimension uses its actual text. We get dimension exactly one, not merely at most one.

3. `lem-kun-compactification-affine` applies to this affine finite-type scheme and explicitly allows its scheme-theoretic closure in projective space; its statement supplies the open dense immersion and dimension equality. I did not assume that an arbitrary dense-open completion is reduced. Instead `lem-trf-reduced-scheme-image` supplies reducedness for this particular scheme-theoretic closure, because U is reduced. The closure of a nonempty irreducible image is irreducible (two relative nonempty opens meet the dense irreducible subset); together with reducedness this is exactly the equivalence in `def-pc-integral-scheme`. The stalk identification follows from the actual open-subscheme isomorphism in `def-weil-open-immersion`. This repairs the potential hidden integrality gap in simply saying “take a projective model”.

4. `lem-kun-projective-implies-proper` states every projective morphism is proper. It applies to the completion's structure map, with no missing hypothesis on the field. The proper-morphism definition explicitly includes finite type, which supplies the finite-type hypothesis for normalization. I use neither a definition node for projective-implies-proper nor an unstated finite-type composition theorem.

5. I wrote the elementary perfectness argument: every irreducible polynomial with an algebraic root has a root in k and therefore is linear. Hence all algebraic extensions are separable, the precise perfectness hypothesis of the normalization node. This works in characteristic zero and positive characteristic; I did not assume that a separably closed field is perfect.

6. `def-sc-normalization` constructs integral closures inside the fixed function field. `lem-sc-integral-function-field-affine-fraction` applies to every nonempty affine chart of integral X and supplies Frac(R)=k(X). The subring Rbar of k(X) is a domain with that same fraction field; all normalization charts share the zero generic point, so integrality and the field identification are explicit. `lem-sc-normalization-properties` really states finite, surjective, birational, proper when X is proper, preservation of dimension, and smoothness in dimension one over a perfect field. I use exactly its properness/dimension/smoothness clauses after checking X integral, finite type and proper in steps 3–4 and k perfect in step 5. Its source is 0BY1/0BY3. Properness of C gives finite type by the cited definition. No clause of the item is moved into a new node.

7. `lemma-nagata-proper-valuative-criterion-existence-api` actually quantifies over every valuation ring with its specified fraction field and every commutative structural square. I instantiate Y=C, S=Spec k, A=B, K=E. The inclusions k into B into E and the k-function-field isomorphism give that square, by the contravariant affine-spectrum statement. The corrected fraction-field hypothesis is essential here. The result is over Spec k and has the prescribed generic restriction, exactly as required. No rank-one, discrete, Noetherian or nontrivial-valuation assumption enters.

I tested E=k(t), where the construction recovers a smooth proper rational curve; positive-characteristic singular affine models, whose normalization is smooth because k is perfect; and B=E, whose valuation extension is the generic map itself. Higher-rank valuation rings require no additional argument because the API imposes no rank bound. The bad case B=k is excluded explicitly by the corrected fraction-field condition. The transcendence-degree-one assumption ensures that the affine model is nonempty and one-dimensional; the proof never assumes E is finite type as a k-algebra.

I checked C1/C4 by opening every cited statement; `citations.json` copies only statement text verbatim, once per step/use. I checked that no uses point to merged nodes and that proof_deps is exactly their union. There are no new nodes to violate B1/B2 or hide a clause of the item (D1/D2); every non-elementary geometric fact has an existing cited node, and the short elementary steps carry their arguments. Every step is shorter than 2000 characters (the longest is below 1000). The off-unit generic tools are declared in `split_report.tool_uses`; they implement the source's construction and do not replace the unit route. Nothing was written outside this sandbox, and no compiler, Lake or build tool was invoked.

## Unfinished work and validation

No part of this stage-1 split is left unfinished. Existing dependency nodes may still require later work; this delivery does not claim new Lean proofs. The server `review_split` check has passed with zero new nodes. Required full dry-run and direct delivery follow this report; their final status is recorded by the delivery tool.
