Files written:

- `dag/nodes/sec-trace-formula/lem-trf-global-operator-triangulated.json` — retained the imported item and repaired its long second proof step by expanding it into four short steps; no new node was needed.
- `citations.json` — verbatim statement quotations for every citation in every proof step.

Attachments:

- None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the blueprint id and global-operator declarations; no sorry-free declaration states this item exactly.

WANTED:

- None. The proof follows the existing blueprint proof text and the existing DAG statements; all cited sources are present locally.

What was wrong and what changed:

- The returned delivery identified step 2 (2296 characters) as a non-elementary step hiding several lemmas. I kept the item statement, its hypotheses, its route, and the other proof steps unchanged. I replaced that step with four short steps: (2) the five-arrow factorization and the formula for `T_c`; (3) typing of all intermediate objects and the bounded étale-origin domain; (4) shift compatibility of the unit, proper comparison, composition comparisons, and exceptional counit; and (5) composition and whiskering of those shift-compatible transformations. The former steps 3 and 4 are now steps 6 and 7, with their calculations unchanged except for the step-number reference.
- Step 3 cites the existing `lem-trf-global-operator-perfect` statement for exactly what it supplies: every intermediate complex in the defining composite is compact-support cohomology of a finite-Tor constructible complex. It also cites `lem-sf-proetale-constructible-origin` for the étale-origin witnesses required by the composition comparisons.
- Step 4 cites all four clauses of the existing `lem-trf-finite-structural-maps-commshift` statement, including the inverse-isomorphism clause and the canonical composite shift for the exceptional inverse image. Step 5 cites the existing Mathlib leaf `lem-weil-pbc-commshift-nattrans-comp-whisker` for composition and both whiskering operations.

## Not duplicates

- No new nodes were created, so no duplicate-node pair exists.

## Review by Q60

I read the retained item against `literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-i-additivity/lem-trf-global-operator-triangulated.proof.md` and the older master node. The statement remains exactly the retained finite-field, finite-coefficient, admissible-correspondence statement, including properness of `c_2`, the finite-Tor category, and the morphism of triangles. I also read the current definitions `def-trf-coefficient-conventions`, `def-trf-correspondence`, `def-trf-admissibility`, and `def-trf-global-operator` in the DAG. In particular, the factorization in repaired step 2 uses the ordinary unit for `Lc_2^* ⊣ Rc_{2*}`, the proper coincidence comparison followed by compact-support composition, and the inverse compact-support composition followed by the exceptional counit, exactly as the global-operator definition states.

For repaired step 3 I read `lem-trf-global-operator-perfect`; its statement explicitly says that every intermediate complex of the defining composite is compact-support cohomology of a finite-Tor constructible complex. I checked that this is the exact typing fact used, rather than importing its proof. I read `lem-sf-proetale-constructible-origin`; its statement says that bounded constructible pro-étale complexes have equivalent bounded étale-origin witnesses, which is the domain condition invoked for compact-support composition. The correspondence hypotheses and properness in the item supply the hypotheses of the perfectness statement.

For repaired step 4 I read the complete statement of `lem-trf-finite-structural-maps-commshift`. Its four clauses cover the proper ordinary unit, proper-coincidence comparison, compact-support composition comparison, and the constructible exceptional counit with the canonical composite shift. The statement also explicitly says that inverses of clauses (2) and (3) satisfy the same shift equation. The schemes and finite coefficient stage in the item match its hypotheses, and `c_1` is separated finite type by admissibility. Thus the step uses only what that node states.

For repaired step 5 I read `lem-weil-pbc-commshift-nattrans-comp-whisker`; its clauses state compatibility under composition, left whiskering, right whiskering, and associativity of composite shift isomorphisms. I checked that these are exactly the operations used to pass from the component maps to `a` and `b`. I read `lem-weil-pbc-commshift-nattrans-triangle-morphism`; repaired step 6 applies its stated conclusion to `a`, `b`, and the induced `H_C` map. The third-square calculation in step 6 explicitly uses the shift naturality equation, and step 7 checks all three component squares and the connecting square using `def-weil-pbc-triangles-with-shift`.

I verified every `uses` entry against the cited node's statement and recorded a verbatim quote for each in `citations.json`. All seven proof-step texts are below 2000 characters (1960, 695, 770, 755, 557, 806, 1007), and no new definition or node was introduced. The retained Mathlib searches remain in `searches.jsonl`; this repair creates no Mathlib node requiring additional searches.

Resumed review on 2026-10-17: I compared the retained sandbox with the current shared item. The statement, Lean record and Lean audit are unchanged; only the long-step replacement and its citations differ. The first required server dry run passed at `5043fc8475`. I then expanded the quotations for steps 1, 2, 3, 4, 5 and 6 so that they contain the actual restrictions, comparisons, equivalence, four structural clauses, and whiskering clauses used, rather than just their introductory sentences.

I reread Stacks `derived.tex`, labels `definition-triangle` (0144), `definition-exact-functor-triangulated-categories` (014V), and `lemma-composition-exact` (014Y), alongside the current blueprint proof. The five-arrow route and all connecting-square calculations are retained. The original source incorrectly calls the initial arrow an exceptional counit: the current global-operator definition and the project definitions `globalOperatorUnit`, `globalOperatorCounit`, and `globalOperator` in `Correspondence.lean:817,841,861` confirm that it is the ordinary unit. Those Lean definitions supply the construction, not the full triangle theorem, so they are not an attachment.

For the B--E self-check, there are no new nodes requiring new definition references, source tags, Mathlib searches, or duplicate comparisons. The hidden arguments now have cited existing nodes: the finite-Tor domains use `lem-trf-global-operator-perfect` (its full intermediate-object clause), etale origin uses clause (ii) of `lem-sf-proetale-constructible-origin`, the geometric shift equations use all four clauses of `lem-trf-finite-structural-maps-commshift`, and closure under composition and whiskering uses `lem-weil-pbc-commshift-nattrans-comp-whisker`. Creating replacement nodes for those facts would duplicate their statements. The final morphism-of-triangles argument remains in the item, so no child restates its conclusion. The intermediate-object lemma has no dependency on this item. Its hypotheses hold even before choosing a coefficient morphism, by taking the zero morphism. Every non-elementary step has the needed statement citations and none exceeds 2000 characters.

I tested the identity correspondence, where the unit, counit and comparison maps reduce to the identity and the conclusion is the given triangle morphism after compact-support cohomology. For zero coefficient morphisms the three operators are zero and all squares commute; the empty correspondence has the same outcome. For a split triangle the three displayed equations reduce to functoriality on its inclusions and projections. Properness is used for the ordinary-leg comparison only, and no inverse of a coefficient morphism is used. These cases preserve the stated hypotheses and reveal no additional assumption.

What remains unfinished:

- The item is a stage-1 natural-language split only; no Lean code was written and no compiler or Lake command was run, as required by the isolated stage-1 instructions.
