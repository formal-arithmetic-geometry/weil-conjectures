# Stage-1 report: prop-trf-graph-operator (Q96)

## Files written

- `dag/nodes/sec-trace-formula/prop-trf-graph-operator.json`: statement, split; Mathlib searches found general adjunction results but no match for the whole graph-operator assertion. The statement is unchanged. Its proof has five steps, with the graph/properness notions added to `stmt_deps`.
- `citations.json`: one verbatim statement excerpt for every cited node in every proof step.
- No new nodes and no new Mathlib leaves. No unit file changed: this proposition specializes the definition in `sk-d-operator`; it is not that unit's key definition.

## Attachments

None. Searched the project `WeilConjectures/` tree for the blueprint id, graph/operator notions, and `globalOperator`. The declarations `AlgebraicGeometry.ProEtale.Correspondence.globalOperatorUnit`, `.globalOperatorCounit`, and `.globalOperator` in `SixFunctors/ProEtale/TraceFormula/Correspondence.lean:817,841,861` construct the general operator; they do not state the graph formula together with naturality, triangle compatibility, and proper composition. They are not attachments for this proposition. The upstream master is reference material, not a finished proof.

## WANTED

None. All documents used were available locally. No SGA source was used.

## Findings and corrections

The imported one-paragraph proof hides the composite-unit equation and all of the final composition calculation behind “unit-counit calculus.” The replacement proof spells out both, including the order of composition: for `v : Lh* K → K`, `w : Lg* K → K`, it proves `T(g,w) T(h,v) = T(h ∘ g, w ∘ Lg*(v))`. This avoids reversing the scheme endomorphisms when contravariant pullback is composed. The proof uses existing statements instead of introducing nodes for the item's clauses or for two-line calculations.

The imported item cites `def-weil-derived-direct-image` and `def-compact-support-direct-image-detailed` as if their definitions supplied proper coincidence and coherent composition. The current statements of those definitions explicitly defer these properties. The split instead cites `prop-functor-package` clause (3), `fix-prop-coherence`, and `fix-prop-adjunctions` clause (3). The latter's current DAG statement gives the correctly typed ordinary composite unit; its older/current-blueprint prose prints an ill-typed expression involving `Lf* η_g Lf*`. I used the already corrected existing DAG statement, checked directly against the composite adjunction formula in `def-weil-pbc-composite-adjunction` and Stacks 0DV0, rather than that expression. This is a source typo, not a change of this item's statement or route.

“Additive in distinguished triangles” is made precise as compatibility with a triangle of coefficient morphisms, including the connecting square. This agrees with the existing statement `lem-trf-global-operator-triangulated`. No trace-additivity claim for arbitrary endomorphisms of Verdier triangles is used or inferred. Its blueprint proof also mistakenly calls the first arrow a counit for the second leg; this split explicitly uses the ordinary adjunction unit, as does the definition and Lean construction. The statement of the cited triangle lemma is the valid assertion used here.

The new blueprint snapshot has moved `sk-lem-sf-mate` from `sec-smooth-purity` to `sec-six-functors-basics`; the source reads below use its actual new path, while existing nodes' maintainer-owned source fields are preserved. No statement dispute for the assigned item was found; no hypotheses or conclusions were altered.

## Not duplicates

No new nodes. Whole-blueprint searches for “graph operator,” “graph construction,” “proper endomorphisms,” and “composition adjunction,” together with whole-DAG keyword searches, found the general naturality/triangle nodes and the ordinary adjunction/composition nodes now reused. `prop-trf-graph-frobenius-operator` is a specialization to Frobenius and its Weil/Galois comparison, not another statement of arbitrary proper graph composition; it is not entered as `same_as` and is not used to prove its prerequisite. `blueprint.same_as` is therefore `[]`.

## Review by Q96

I read the contract, worker role, stage-1 brief and stage document, SETUP's three levels, GOAL, DAG-sync instructions, the chapter and `sk-d-operator` unit records, and delivery-errors B–E. The unit defines the operator through the unit, proper comparison and exceptional counit; it has no proof steps to replace. This split follows exactly that route and expands only its graph specialization. Generic operation-package and triangle tools outside this unit are individually declared in `split_report.tool_uses`.

For the item I read the current `literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-d-operator/prop-trf-graph-operator.md` and its separate proof. I compared the older imported item and inspected the Lean general operator construction at `Correspondence.lean:807–866`. For the sources of reused tools I read the current naturality and triangulated node statements, the current `prop-functor-package` proof and `fix-prop-coherence` statement, and the current `sec-six-functors-basics/sk-lem-sf-mate/fix-prop-adjunctions` statement and proof. I also read `literature/stacks-project/categories.tex`, label `lemma-compose-counits`, and checked the tag map gives 0DV0; I read `morphisms.tex`, label `lemma-composition-proper` (01W3), for the properness premise of Step 4. There are no new-node sources to certify.

Step 1 uses the **statements**, opened in full, of `def-trf-graph-correspondence` (identity exceptional leg and ordinary leg h), `def-trf-global-operator` (the displayed unit/proper/coefficient/counit composite), `def-weil-pbc-composite-adjunction` (the identity adjunction has identity counit), and `prop-functor-package` (proper coincidence and unital compact-support composition). The global finite-field and finite coefficient datum is inherited from the graph definition, so h is a k-morphism and a_X h = a_X. Its properness is exactly what permits replacing Rh_* with Rh_!. This is valid even when X/k is not proper. The identity leg's exceptional inverse image is identified with identity using its identity adjunction, with no purity theorem.

Step 2 uses the **statement** of `lem-trf-global-operator-naturality`, which states the square for a morphism of coefficient pairs, not merely a definition of such pairs. Its proper-leg hypothesis is h's hypothesis and its exceptional leg is identity, hence admissible. I wrote the pair condition f v = v' Lh*(f) and the induced square. Naturality of q for an arbitrary underlying coefficient map is the componentwise naturality of the unit and the canonical comparison isomorphisms displayed in Step 1; it does not require an invertible coefficient map.

Step 3 uses the **statement** of `lem-trf-global-operator-triangulated`: it explicitly gives a morphism of the compact-cohomology distinguished triangles for a triangle morphism from Lc_2* to Rc_1!. Setting c_1 = id and c_2 = h gives precisely the coefficient triangles used here, including the fourth arrow. I did not take any fact from the flawed wording of that node's proof. There is no trace assertion in this step.

Step 4 uses the **statement** of `lem-weil-pbc-proper-composition` to know h ∘ g is proper, the exact unit formula in clause (3) of **the current DAG statement** of `fix-prop-adjunctions`, and clause (3) of `prop-functor-package` plus the **statement** of `fix-prop-coherence` to replace direct images by proper compact-support images and collapse the associative composition comparisons. The definition `def-weil-pbc-composite-adjunction` supplies the identity case. All of h,g are separated finite-type morphisms between the same finite-type k-scheme, and K and its pullbacks remain in the finite constructible domains specified by the graph/operation package. No adic, discrete non-torsion, or arbitrary ambient exceptional-adjoint assertion is used. I verified the formula η_(h∘g) = Rh_*(η_g at Lh*K) η_h is typed K → Rh_*Rg_*Lg*Lh*K. The text also expands the naturality square for the proper/composition comparison b_h on η_g, so collapsing the two unit insertions is an actual component calculation. After H and the proper comparisons it has source H(K) and target H(Lg*Lh*K), so the order in q_(h∘g) = q_g(at Lh*K) q_h is forced.

Step 5 is an elementary calculation from the previous steps, not a new lemma or an uncited theorem: substitute the two formulas from Step 1, use q_g's naturality on v (from Step 2), then use Step 4 and functoriality to combine H(w) followed after H(Lg*(v)) in the displayed order. Associativity of the resulting operators is ordinary categorical associativity; the same canonical pullback comparisons are those already covered in Step 4. Thus no fact is hidden in “compatible with composition.”

I tested the identity endomorphism (q_id = id and T_id,v = H(v)); the zero complex and zero coefficient map (the resulting operator is zero); and a split coefficient triangle (the displayed construction is block diagonal). As an order check, on a finite disjoint union of points and constant coefficients with identity coefficient maps the operator is precomposition by h on sections; applying h then g on sections is precomposition by h ∘ g, agreeing with Step 5 even for noncommuting maps. These checks require neither h to be an automorphism nor v to be invertible. No new statement has small cases to test.

I checked every citation against its node's statement and wrote the used formula/sentence verbatim into `citations.json`. I also followed the dependencies of the reused general triangle, naturality, adjunction and package tools: none depends on this item. The split therefore does not prove itself through a more specialized graph/Frobenius theorem. All Mathlib search entries are actual logged `msearch.py` queries; both semantic phrasings were read, and all services used returned answers. General adjunction composition is present in Mathlib, but there is no one-line specialization stating this project's compact-support graph construction and all its clauses. With no new nodes, there is no falsely unsplit elementary fact, duplicate, or relabelled clause to deliver.

## Unfinished work

None in the one-level split. The required dry run is the final check; this sandbox is for the independent second reader, and has not been pushed.

## Second reading by Q96

- Item statement: checked against the current blueprint `main-20261015/.../prop-trf-graph-operator.md`; the graph, properness, operator composite, functoriality, triangle compatibility, and proper-composition clauses agree, with no hypothesis or conclusion changed.
- Step 1: checked against the statements of `def-trf-global-operator`, `def-trf-graph-correspondence`, `def-weil-pbc-composite-adjunction`, and clause (3) of `prop-functor-package`; the identity exceptional leg, proper comparison, and compact-support composition give exactly the displayed unit followed by (H(v)).
- Step 2: checked against `lem-trf-global-operator-naturality`; its morphism-of-correspondences square supplies the coefficient-pair naturality condition and does not require (f) to be invertible.
- Step 3: checked against `lem-trf-global-operator-triangulated`; its stated morphism of compact-cohomology triangles supplies all three squares and the connecting-arrow square after specializing (c_1=\operatorname{id}), (c_2=h).
- Step 4: checked against `lem-weil-pbc-proper-composition`, clause (3) of `fix-prop-adjunctions`, clause (3) of `prop-functor-package`, `fix-prop-coherence`, and `def-weil-pbc-composite-adjunction`; the composite-unit formula and comparison coherence are typed in the order (q_{h\circ g}=q_g(Lh^*K)q_h).
- Step 5: checked as the explicit calculation from Steps 2 and 4; pullback contravariance gives (w\circ Lg^*v), and the displayed operator equality has the correct order and identity case.
- New nodes: none; the whole DAG and blueprint were searched for graph-operator, global-operator, proper-composition, and Frobenius specializations, and all reusable facts were existing nodes.
- Source and edge cases: reread the blueprint proof and the cited node statements, and tested identity and zero maps, zero complexes, split triangles, and noncommuting proper endomorphisms on a finite disjoint union of points; no statement dispute or source correction was found.
- Changes made in this second reading: appended this review section only; no node, citation, or search record required repair.
