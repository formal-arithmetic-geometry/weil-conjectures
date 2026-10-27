# Stage-1 repair: lem-sfb-wcontractible-component-derived-hom

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-wcontractible-component-derived-hom.json: existing statement unchanged, split into a short assembly.
- dag/nodes/sec-six-functors-basics/lem-sfb-component-pullback-unbounded-evaluation.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-component-pushforward-exact-unit.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-component-slice-hom-comparison-test.json: statement, unsplit; no Mathlib match.
- citations.json: a verbatim statement quote for every citation in every parent step.

## Attachments

None. The read clone has no WeilConjectures declaration tagged with the item. The live Sheaf.Paper.WContractibleComponentDerivedHom theorem AlgebraicGeometry.ProEtale.CondensedRing.wContractible_component_derived_hom at line 163 ends in sorry at line 220. I read its statement and docstring: it covers precisely the component functor and all three requested consequences, but is unfinished. Its additional normalization data are consistent with the evaluation-normalized comparisons retained here.

## WANTED

None. Hemo–Richarz–Scholbach, Constructible sheaves on schemes, Section 3 and Proposition 4.3(1), including equation (4.2), and Stacks sites-cohomology.tex are present locally and were read.

## What was wrong and what changed

The returned nine-step proof concentrated about 7,447 characters of work in one node. The sandbox initially contained only dispatcher brief markers, with no node, report or searches. I copied the current repository node, which contains the returned nine steps, and retained its statement, citations, existing searches and all maintainer-owned fields. returned-proof-baseline.json preserves this exact baseline. I have not treated a transport failure or missing prior final answer as invalidating that proof. No statement dispute or route replacement is involved.

The repair creates three statement-only tasks, each with its own hypotheses, sources, provenance, and actual logged searches. They are not the three clauses of the parent: the first is a coefficient-linear evaluation formula, the second is a theorem about the ordinary right adjoint and its unit, and the third is a normalized slice calculation with an explicit conditional full-faithfulness hypothesis. The parent still derives full faithfulness by localizing the exact adjunction and still proves the internal-Hom isomorphism by the cone argument. In particular none of the new statements simply asserts the parent's global internal-Hom preservation.

## Allocation of every old argument

| Returned step | Where its work now lives |
| --- | --- |
| 1: coefficients, exact inverse image, adjunction, monoidal derived pullback, evaluation transpose | Parent step 1, unchanged. |
| 2: geometry of W_E, closed points, local rings, empty case | component-pushforward-exact-unit, the component-test assertion. The existing profinite-component-ring-pullback theorem already gives the w-local geometry; strict henselian local rings and extremal disconnectedness give w-contractibility. |
| 3: split covers, module evaluation and scalar action, slice localization, exact evaluations, termwise unbounded sections | component-pullback-unbounded-evaluation. |
| 4: Stonean tests detect exactness; G(N)(E)=N(W_E); unit is identity on M(E) | component-pushforward-exact-unit. |
| 5: exact derived adjunction, localized unit, explicit inverse on Hom sets; repeat for every U | Parent step 3, including the inverse formula and its justification. |
| 6: U=W gives pullback-normalized derived global sections | Parent step 2 using the normalization explicitly stated in component-pullback-unbounded-evaluation. |
| 7: restriction comparison on every V over U, restriction maps/scalars, basis argument and evaluation normalization | component-slice-hom-comparison-test, its first functor isomorphism and normalization. |
| 8: sections of the actual Hom comparison, slice transpose, shifted Hom map f maps to pullback f, full faithfulness | component-slice-hom-comparison-test, with its explicit implication from full faithfulness of F_U; parent step 4 supplies that hypothesis from step 3. |
| 9: cone, exact basis evaluation, vanishing cohomology sheaves, naturality and unrestricted inputs | Parent step 5. |

The full returned argument is reproduced below verbatim, so the future workers on these statement-only tasks retain the arguments and citations rather than a shortened paraphrase. The new node files deliberately have no proof steps or proof dependencies.

## Review by Q68

For the landing-refusal repair of returned head `04d3d8852be`, I compared the retained delivered files against the current read clone and the retained pre-split baseline. The current item is exactly that baseline, including its old nine steps and maintainer metadata; the three support nodes are still absent from the live DAG. Thus the previous reader-approved split still has substantive work to deliver. The released stage-1 repair note expressly requires at least two new tasks and a short assembly, even though the old node has a historical passing review. I retained all three tasks, existing searches, citations, full old proof and allocation table. The delivery script builds the repair on current `origin/sheaf-dag`; I did not run git in the shared repository.

I re-read every existing statement used by the five retained steps against the current DAG, rather than relying on the earlier review. Step 1 still has the actual component factorization, exact inverse image with transported coefficients, module adjunction, and canonical derived tensor comparison; the coefficient map is an isomorphism, as required to identify ordinary and derived pullback. Step 2 uses the retained evaluation task's normalized whole-object derived comparison. Step 3 uses the retained exact-unit task and the current exact-derived-adjunction statement, which still explicitly localizes the units and counits. Its Hom inverse and the triangle identities give full faithfulness on each affine U. Step 4 uses the retained slice-test task only after that hypothesis has been established; its comparison is the actual evaluation transpose, with the shifted map f sent to F_U(f). Step 5 uses exact evaluation from the retained task and the current basis theorem's covering clause. I checked every entry of citations.json against these current statement texts; none needs replacement. The old proof's additional component-geometry and slice lemmas were also reread to verify that the retained task allocation still has the hypotheses it needs.

I reopened Hemo–Richarz–Scholbach Proposition 4.3(1), construction (4.1), equation (4.2), and the entire proof of (1): the source tests the unit on extremally disconnected E, proves W_E w-contractible using its closed points and unchanged local rings, and obtains internal Hom from full faithfulness and (4.2). For the slice task I reopened Stacks Tags 08JA and 08JB and their proofs. Their actual formulas give slice derived Hom and its restriction, without boundedness. I checked the current profinite-component-ring-pullback statement for its w-local and local-ring assertions. These checks preserve the original route and all original arguments. Empty objects, the zero coefficient ring, and unbounded inputs still satisfy every retained hypothesis. All five parent steps have fewer than 2000 characters and their total is 2409 characters. The initial required dry run passed at `88b8fb21a4b`; the report and split_report now explicitly document this landing-refusal repair, and a fresh final dry run is required before pushing. `landing-repair-audit.json` records hashes of the current cited nodes for this comparison. The assembly itself now writes both Hom-inverse identities using unit/counit naturality and the triangle identity, and states that exact termwise evaluation preserves cone triangles. These are explicit checks from the cited exact adjunction and evaluation statements, without adding a lemma, weakening a statement or hiding work in a new task.


I read the fixed chapter and the stability unit, and the inherited chain into its open-direct-image work. This is still the same external component-site tool for that route. blueprint_refs.py ancestor returns a null ancestor for the existing historical chain; I retain the item's null from.node and record the same value with the item prepended to via in the children. Searches of the whole imported blueprint for component pullback, component adjunction, component evaluation and internal Hom comparison found no identical statement. DAG searches included all component-node titles, the same HRS source place, and the relevant Stacks tags. No target, definition, unit route or coefficient category is changed.

For the item and both component evaluation and component adjunction tasks I read HRS Section 3, construction (4.1), Proposition 4.3(1) and its proof through (4.2). In that proof the sheafification formula is only a section formula on w-contractible tests, not on arbitrary affines. I preserved that restriction. I opened the affine-component-site-projection statement: it requires the split-cover condition and gives naturality for abelian sheaves and rings. The old clopen-partition step supplies that condition and naturality applied to the scalar-action map supplies linearity. The new evaluation node states the full derived-object isomorphism, not only a list of cohomology group isomorphisms. Exact evaluation, rather than an assumption about bounded-below resolutions, gives the unbounded conclusion. I opened the contractible-derived-sections-tensor statement to verify that it accepts any sheaf of commutative rings. Only the site-equivalence clause of the weakly-etale-localization theorem is used; its separate discrete-coefficient clauses are not used for condensed rings.

For the adjunction task I read the full statements of component-relative-profinite-site, affine-component-site-projection and profinite-component-ring-pullback. The last theorem already gives the w-local closed points and local-ring isomorphisms under profinite component pullback. Thus W_E is w-strictly local, and E extremally disconnected makes it w-contractible. No arbitrary scheme base-change property is being substituted here: W_E is the specific affine component construction. Evaluation on W_E is exact by the evaluation task and the contractible-sections theorem. Stonean covers are covers over S after composition, and exactness and isomorphism detection on these tests follow from the sheaf condition. The component map of W_E is the identity on E, so the adjunction unit, not just an unspecified isomorphism, is identified with the identity M(E).

For the slice task I read HRS's final sentence of the proof and Stacks Tags 08JA (lemma-section-RHom-over-U) and 08JB (lemma-restriction-RHom-to-U) in sites-cohomology.tex, including their proofs. I also opened the full statements of ringed-internal-hom-exact-restriction, derived-internal-hom-sections-model, ringed-slice-evaluation-transpose and ringed-derived-closed-symmetric-monoidal. The transpose theorem explicitly provides the restriction/evaluation identity, not merely the existence of a slice isomorphism. On the w-contractible basis V over U, both functors use the same maps pi_0(V) to T to S and the same scalar action, so this is a canonical restriction identification, compatible with tensor and evaluation. The new node states that the actual derived-sections morphism is identified with that local transpose, with f sent to F_U(f) in all shifts. It does not assume preservation of internal Hom in order to prove that identification, and does not assert the parent's conclusion without the explicit local full-faithfulness hypothesis.

Parent step 1 cites the component morphism for its factorization, geometric-inverse-image-exact for exactness with transported scalars, ringed-topoi-module-adjunction for precisely F adjoint G, and ringed-topoi-derived-tensor-pullback for the canonical tensor comparison. I read each complete cited statement. The coefficient map is an isomorphism, so the exactness claim does not rely on tensoring with an arbitrary nonflat new coefficient ring. Step 2 cites the new evaluation theorem, which explicitly states the global-sections specialization and its canonical pullback normalization. Step 3 cites the new exact-unit theorem and exact-derived-adjunction: the latter explicitly says that units localize degreewise. Its remaining full-faithfulness argument is elementary and written out with its inverse and triangle identities. Step 4 cites the new slice test, which gives the precise comparison and conditional isomorphism used there; step 3 establishes that condition for every U before it is used. Step 5 cites the evaluation theorem for exact evaluation on W, rather than implicitly transferring exactness from U without citing localization, and the weakly-contractible-basis theorem for the covering assertion. Vanishing sections then kill cohomology sheaves by the sheaf condition. Every cited statement is copied verbatim into citations.json; none is only a definition of the theorem being invoked.

I tested empty W, U and E: evaluation is zero for modules on the empty site, the empty clopen partition is allowed, and the terminal unit formula is still the identity. The zero ring and zero complexes cause no exception. I also checked unbounded K and L, non-discrete Lambda and infinite profinite tests: exact evaluation and whole-derived-category localization never use truncation, finite generation, t-admissibility, perfectness or dualizability. New node statements introduce all objects and do not use tags to define their meaning. They are all unsplit with empty proof and proof_deps. All parent steps are below 2,000 characters and the total parent proof is below 3,000 characters.

The Mathlib searches in searches.jsonl are real msearch invocations: LeanFinder in two phrasings per task, Loogle and grep, with LeanSearch attempts honestly marked unavailable because of its rate limit. I read the logged hits and inspected candidates by msearch grep. CondensedMod.ofSheafStonean/Profinite are sheaf constructors; isSheafProfinite is a site presentation; sheafHomSectionsEquiv is ordinary categorical sheaf Hom; restrictFunctorIsoPullback concerns ordinary scheme-module restriction. None states any of the three new claims for component morphisms with arbitrary condensed coefficients and unbounded complexes. No Mathlib leaf is claimed.

## Not duplicates

lem-sfb-component-pullback-unbounded-evaluation vs def-zl-condensed-lisse-evaluation-model: this node gives exact evaluation and coefficient-linear pullback sections for every module sheaf and unbounded complex on Prof/S; the existing node gives a component construction, a lisse/perfect model, or sections only for a prescribed scalar-realized family, not this formula.

lem-sfb-component-pullback-unbounded-evaluation vs lem-sfb-wcontractible-component-derived-hom: the parent is a global derived closedness/full-faithfulness theorem; this task states module-linear exact evaluation on tests.

lem-sfb-component-pullback-unbounded-evaluation vs lem-sfb-wstrict-lisse-component-cohomology: this node gives exact evaluation and coefficient-linear pullback sections for every module sheaf and unbounded complex on Prof/S; the existing node gives a component construction, a lisse/perfect model, or sections only for a prescribed scalar-realized family, not this formula.

lem-sfb-component-pullback-unbounded-evaluation vs lem-zl-condensed-affine-ordinary-scalar-sections: this node gives exact evaluation and coefficient-linear pullback sections for every module sheaf and unbounded complex on Prof/S; the existing node gives a component construction, a lisse/perfect model, or sections only for a prescribed scalar-realized family, not this formula.

lem-sfb-component-pullback-unbounded-evaluation vs lem-zl-condensed-component-pullback-compatibility: this node gives exact evaluation and coefficient-linear pullback sections for every module sheaf and unbounded complex on Prof/S; the existing node gives a component construction, a lisse/perfect model, or sections only for a prescribed scalar-realized family, not this formula.

lem-sfb-component-pullback-unbounded-evaluation vs lem-zl-condensed-wcontractible-lisse-evaluation: this node gives exact evaluation and coefficient-linear pullback sections for every module sheaf and unbounded complex on Prof/S; the existing node gives a component construction, a lisse/perfect model, or sections only for a prescribed scalar-realized family, not this formula.

lem-sfb-component-pullback-unbounded-evaluation vs lem-zl-wcontractible-condensed-scalar-evaluation: this node gives exact evaluation and coefficient-linear pullback sections for every module sheaf and unbounded complex on Prof/S; the existing node gives a component construction, a lisse/perfect model, or sections only for a prescribed scalar-realized family, not this formula.

lem-sfb-component-pushforward-exact-unit vs def-zl-condensed-lisse-evaluation-model: this node is about ordinary component direct image, exactness and the normalized adjunction unit on every module sheaf; the existing node concerns component construction, scalar/lisse realization, or derived Hom and does not state that exact-unit theorem.

lem-sfb-component-pushforward-exact-unit vs lem-sfb-wcontractible-component-derived-hom: the parent asserts derived consequences; this task proves the ordinary right-adjoint exactness and identifies its actual unit on Stonean tests.

lem-sfb-component-pushforward-exact-unit vs lem-sfb-wstrict-lisse-component-cohomology: this node is about ordinary component direct image, exactness and the normalized adjunction unit on every module sheaf; the existing node concerns component construction, scalar/lisse realization, or derived Hom and does not state that exact-unit theorem.

lem-sfb-component-pushforward-exact-unit vs lem-zl-condensed-affine-ordinary-scalar-sections: this node is about ordinary component direct image, exactness and the normalized adjunction unit on every module sheaf; the existing node concerns component construction, scalar/lisse realization, or derived Hom and does not state that exact-unit theorem.

lem-sfb-component-pushforward-exact-unit vs lem-zl-condensed-component-pullback-compatibility: this node is about ordinary component direct image, exactness and the normalized adjunction unit on every module sheaf; the existing node concerns component construction, scalar/lisse realization, or derived Hom and does not state that exact-unit theorem.

lem-sfb-component-pushforward-exact-unit vs lem-zl-condensed-wcontractible-lisse-evaluation: this node is about ordinary component direct image, exactness and the normalized adjunction unit on every module sheaf; the existing node concerns component construction, scalar/lisse realization, or derived Hom and does not state that exact-unit theorem.

lem-sfb-component-pushforward-exact-unit vs lem-zl-wcontractible-condensed-scalar-evaluation: this node is about ordinary component direct image, exactness and the normalized adjunction unit on every module sheaf; the existing node concerns component construction, scalar/lisse realization, or derived Hom and does not state that exact-unit theorem.

lem-sfb-component-slice-hom-comparison-test vs def-coef-hom-zero-cycle-class: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs def-coef-semilinear-derived-calculus: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs def-per-ordinary-kummer-first-chern: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs def-pur-external-rhom-pairing-interface: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs def-pur-ringed-site-zeroth-hypercohomology: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs def-sfb-internal-slice-derived-hom-comparison: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs def-sfb-ringed-slice-comparison-model: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs def-weil-pbc-adic-global-derived-hom: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs def-weil-pbc-ringed-derived-restriction: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs def-weil-pbc-ringed-presentation-comparison-data: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs def-zl-condensed-lisse-evaluation-model: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-coef-etale-hom-transpose-exact: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-coef-rational-bidual-triangle-compatibility: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-coef-scalar-hom-zero-compatibility: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-coef-semilinear-operations-existence: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-coef-semilinear-system-existence: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-coef-signed-single-dual-restriction: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-coef-slice-hom-source-shift: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-pc-derived-pullback-evaluation-sections: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-pc-derived-tensor-hom-sections-unit: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-pur-derived-internal-hom-shift-comparison: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-pur-derived-internal-hom-shift-left: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-pur-derived-internal-hom-shift-right: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-pur-external-evaluation-transpose-natural: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-pur-external-rhom-derived-braiding: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-pur-external-rhom-signed-cones: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-pur-global-hom-evaluation-model: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-pur-hom-complex-global-homotopy: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-pur-hom-complex-hypercohomology: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-pur-hom-complex-resolution-shift-comparison: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-pur-hom-kflat-into-kinjective: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-pur-rhom-global-sections: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-sc-global-hom-shifted-hypercohomology: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-sc-restricted-global-hom-shifted-equiv: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-sfb-derived-internal-hom-sections-model: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-sfb-module-object-ringed-site-derived-comparison: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-sfb-open-closed-internal-hom-formulas: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-sfb-wcontractible-component-derived-hom: the parent concludes a global comparison is invertible; this task identifies its slice map and only conditionally asserts a local isomorphism from local full faithfulness.

lem-sfb-component-slice-hom-comparison-test vs lem-sfb-wstrict-lisse-component-cohomology: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-weil-pbc-derived-hom-sheaf-comparison-lisse: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-weil-pbc-element-restriction-hom: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-weil-pbc-kflat-rhom-currying: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-weil-pbc-proetale-internal-hom-lower-bound: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-weil-pbc-ringed-augmented-cech-restriction: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-weil-pbc-ringed-cech-completion-restriction: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-weil-pbc-ringed-cech-koszul-comparison-existence: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-weil-pbc-ringed-cech-koszul-dual-limit: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-weil-pbc-ringed-complete-elements-locality: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-weil-pbc-ringed-internal-hom-exact-restriction: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-weil-pbc-ringed-localization-complex-models: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-weil-pbc-ringed-localization-factor-restriction: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-weil-pbc-ringed-localization-natural-currying: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-weil-pbc-ringed-localization-rhom-calculus: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-weil-pbc-ringed-model-currying: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-weil-pbc-ringed-model-currying-coherence: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-weil-pbc-ringed-model-restriction: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-weil-pbc-ringed-slice-evaluation-coherence: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-weil-pbc-ringed-slice-evaluation-transpose: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-weil-pbc-ringed-slice-normalized-comparisons: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-weil-pbc-ringed-slice-representative-evaluation: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-weil-proetale-derived-restriction-closed-monoidal: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-zl-condensed-affine-ordinary-scalar-sections: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-zl-condensed-component-pullback-compatibility: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-zl-condensed-wcontractible-lisse-evaluation: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

lem-sfb-component-slice-hom-comparison-test vs lem-zl-wcontractible-condensed-scalar-evaluation: this node relates the component functors on two different sites and identifies the actual evaluation-adjoint sections map on every shifted Hom; the existing node gives a single-site slice/internal-Hom statement or a lisse/scalar component statement, without this component comparison.

## What remains unfinished

The three new theorem nodes intentionally remain unsplit for parallel stage-1 work, as the return instructs. No Lean was written and no compiler or Lake was run. The parent is a complete assembly assuming these statements. Server dry run and delivery results are recorded after they finish.

## Retained returned proof, verbatim

### Returned step 1

Write $F=\pi_W^*$ and $G=\pi_{W,*}$ on module sheaves. The factorization $p_W=q_S\pi_W$ identifies $F\Lambda_S$ with $p_W^*\Lambda$, so the coefficient map is an isomorphism. The geometric inverse-image exactness theorem makes $F$ exact; the ringed-topos module adjunction supplies $F\dashv G$. The derived tensor pullback theorem makes its termwise derived functor strong symmetric monoidal, with the usual unit comparison. Thus the comparison in the statement is defined by pulling back evaluation and taking its tensor-Hom transpose.

Cited nodes: lem-zl-component-relative-profinite-site, lem-trf-geometric-inverse-image-exact, lem-weil-pbc-ringed-topoi-module-adjunction, lem-weil-pbc-ringed-topoi-derived-tensor-pullback

Source: literature/hemo-richarz-scholbach-constructible-sheaves_arXiv-2305.18131.pdf; Section 3, derived pullback paragraph; construction (4.1), coefficient factorization and Proposition 4.3(1)

### Returned step 2

Let $E\to S$ be an extremally disconnected profinite test object and put $W_E=W\times_S E$. The affine component-site theorem gives the affine scheme $W_E$, its component space $E$, and the locally ringed space $|W|\times_S E$ with structure sheaf pulled back from $W$. Its closed points are precisely $(c,e)$ with $c$ closed in $W$: the closure of $(w,e)$ is $\overline{\{w\}}\times\{e\}$ inside this fibre product, since $E$ is Hausdorff and specialization stays in a component of $W$. Every $(w,e)$ therefore specializes to exactly $(c(w),e)$, and this closed-point locus is the closed subset $W^c\times_S E$. Its local rings are the corresponding local rings of $W$, hence strictly henselian. Together with $\pi_0(W_E)=E$, the definition of w-contractibility proves that $W_E$ is w-contractible. This includes $E=\varnothing$.

Cited nodes: lem-zl-affine-component-site-projection, sk-def-pe-wlocal

Source: literature/hemo-richarz-scholbach-constructible-sheaves_arXiv-2305.18131.pdf; Proposition 4.3(1), proof: the paragraph proving that X times over pi_0(X) S is w-contractible; Bhatt–Scholze Lemmas 2.2.8 and 2.4.8

### Returned step 3

Let $U\to W$ be any w-contractible affine and put $T=\pi_0(U)$. The clopen-partition theorem splits each finite qcqs covering family over $U$: glue the maps from its disjoint clopen pieces into the coproduct of the covering members. Thus $U$ satisfies the split-cover condition in the affine component-site theorem. For a module sheaf $M$ on $\operatorname{Prof}/S$, that theorem gives $(FM)(U)=M(T)$ on underlying abelian groups. Its naturality in abelian sheaves and rings identifies the action too: apply it to the scalar-action map, so the two section groups have the same $\Lambda(T)$-module structure. By the site-equivalence clause (1) of the weakly-etale localization theorem, evaluation at the object $U$ of $W_{\mathrm{proet}}$ on module sheaves is evaluation of the restriction to $W_{\mathrm{proet}}/U\simeq U_{\mathrm{proet}}$ at its terminal object, with the restricted ring sheaf; the contractible-sections theorem allows any ring sheaf. Evaluation at $U$ and at the extremally disconnected $T$ is therefore exact and its termwise functor computes unbounded derived sections by the contractible-sections theorem. Apply the preceding equality in each degree of an arbitrary complex representing $K$ to obtain the natural derived-category isomorphism
$$R\Gamma(U,FK)\cong R\Gamma(T,K|_T).$$
This is (4.2), with restriction to the profinite slice over $T$ understood; it is an isomorphism of entire derived objects, not merely of their cohomology groups.

Cited nodes: det-pe-wcb-clopen-partition, lem-zl-affine-component-site-projection, sk-def-pe-wlocal, lem-weil-proetale-weakly-etale-localization, lem-zl-contractible-derived-sections-tensor

Source: literature/hemo-richarz-scholbach-constructible-sheaves_arXiv-2305.18131.pdf; Proposition 4.3(1), proof through equation (4.2)

### Returned step 4

Every profinite $S$-set is covered by an extremally disconnected one: use its Stonean cover and compose the map with its structure map to $S$. Such tests detect isomorphisms and zero sheaves, by the sheaf condition. By the definition of direct image for the component-site functor,
$$(GN)(E)=N(W_E).$$
For a short exact sequence of module sheaves on $W$, evaluation at $W_E$ is exact by step 2 and step 3 (applied to the w-contractible object $W_E\to W$). Hence $G$ carries it to a sequence exact on every extremally disconnected test, and therefore to an exact sequence of sheaves. In particular $G$ is exact. For every $M$, the ordinary adjunction unit $M\to GFM$ evaluates at $E$ to
$$M(E)\longrightarrow(FM)(W_E)=M(\pi_0(W_E))=M(E).$$
This is the identity: the component map of the test object $W_E$ is the identity of $E$. Hence the unit is an isomorphism.

Cited nodes: det-pe-stonean-cover, lem-zl-component-relative-profinite-site, lem-zl-contractible-derived-sections-tensor

Source: literature/hemo-richarz-scholbach-constructible-sheaves_arXiv-2305.18131.pdf; Proposition 4.3(1), proof: evaluation of the unit on extremally disconnected profinite S

### Returned step 5

Localize the exact adjunction $F\dashv G$ degreewise, as in the exact-derived-adjunction definition. Both derived functors are induced termwise and the derived unit is the localized ordinary unit, hence an isomorphism by step 4. Consequently $D(F)$ is fully faithful. Explicitly the inverse to its map on Hom sets sends $a:FK\to FL$ to $\eta_L^{-1}\circ D(G)(a)\circ\eta_K$; naturality of $\eta$ and the adjunction triangle identities show both composites are identities. The argument in steps 1–5 applies to every w-contractible affine, so in particular it proves full faithfulness for $\pi_U^*$ whenever $U$ is such an affine. This establishes that assertion before it is used below.

Cited nodes: def-weil-exact-derived-adjunction

Source: literature/hemo-richarz-scholbach-constructible-sheaves_arXiv-2305.18131.pdf; Proposition 4.3(1), proof: id to pi_* pi^* is an equivalence, which formally implies full faithfulness

### Returned step 6

Taking $U=W$ in the derived evaluation isomorphism of step 3 yields
$$R\Gamma(W,\pi_W^*K)\cong R\Gamma(S,K).$$
The inverse is the canonical pullback map on sections: the termwise evaluation equality was induced by the component-site adjunction unit. Thus this proves the requested comparison in the derived category, naturally in every unbounded $K$.

Cited nodes: 

Source: literature/hemo-richarz-scholbach-constructible-sheaves_arXiv-2305.18131.pdf; Equation (4.2), specialized to U=X

### Returned step 7

Fix a w-contractible affine $U\to W$ and put $T=\pi_0(U)$. Identify $U_{\mathrm{proet}}$ with $W_{\mathrm{proet}}/U$ using the weakly-etale localization theorem (its site-equivalence clause does not require discrete coefficients). The profinite slice at $T\to S$ is $\operatorname{Prof}/T$. On every w-contractible affine $V\to U$, both $(\pi_W^*K)|_U$ and $\pi_U^*(K|_T)$ evaluate, by step 3, to $R\Gamma(\pi_0(V),K|_{\pi_0(V)})$. These identifications come from the same component maps $\pi_0(V)\to T\to S$; they respect restrictions and scalar actions. The w-contractible affine covering basis therefore gives the canonical restriction identification
$$(\pi_W^*K)|_U\cong\pi_U^*(K|_T).$$
It is already an identification of exact functors on sheaves, so applying it termwise proves the displayed derived comparison and its naturality. Its tensor and evaluation normalizations are the canonical ones, since both are induced from the same inverse-image functors and coefficient identifications.

Cited nodes: lem-weil-proetale-weakly-etale-localization, sk-thm-pe-weakly-contractible-basis

Source: literature/hemo-richarz-scholbach-constructible-sheaves_arXiv-2305.18131.pdf; Proposition 4.3(1), final sentence of proof, using (4.2) after restriction to U

### Returned step 8

Write $H_S=R\mathcal Hom_{\Lambda_S}(K,L)$ and let $\alpha:FH_S\to R\mathcal Hom(FK,FL)$ be the comparison of step 1. On the w-contractible $U$ of step 7, equation (4.2) and the restriction theorem for derived internal Hom identify its derived sections with a map
$$R\Gamma(T,R\mathcal Hom(K|_T,L|_T))\longrightarrow R\Gamma(U,R\mathcal Hom(\pi_U^*K|_T,\pi_U^*L|_T)).$$
For every $n\in\mathbf Z$, the derived-internal-Hom sections model identifies the $n$th cohomology groups with $\operatorname{Hom}(K|_T,L|_T[n])$ and $\operatorname{Hom}(\pi_U^*K|_T,\pi_U^*L|_T[n])$. Under these identifications the map is exactly pullback by $\pi_U^*$. Indeed the comparison is the transpose of pulled-back evaluation; the slice-evaluation-transpose theorem identifies its restriction with that transpose on the slice. A class represented by $f:K|_T\to L|_T[n]$ therefore goes to $\pi_U^*f$, by the tensor-Hom counit formula. Full faithfulness proved in step 5 for $U$ makes this a bijection for every $n$, so $R\Gamma(U,\alpha)$ is an isomorphism of derived objects.

Cited nodes: lem-weil-pbc-ringed-internal-hom-exact-restriction, lem-sfb-derived-internal-hom-sections-model, lem-weil-pbc-ringed-slice-evaluation-transpose, lem-sf-ringed-derived-closed-symmetric-monoidal

Source: literature/hemo-richarz-scholbach-constructible-sheaves_arXiv-2305.18131.pdf; Proposition 4.3(1), final sentence: preservation of inner homomorphisms from full faithfulness and (4.2); expanded with Stacks Tags 08JA and 08JB

### Returned step 9

Let $C$ be a cone of $\alpha$. Step 8 gives $R\Gamma(U,C)=0$ for every w-contractible affine $U\to W$. Exact evaluation on each such $U$ (step 3) gives $\Gamma(U,H^n(C))=H^nR\Gamma(U,C)=0$ for all integers $n$. Every pro-etale object has a cover by these affines, so the sheaf condition gives $H^n(C)=0$. Thus $C=0$ and $\alpha$ is an isomorphism in the ordinary unbounded derived category. All maps used above are induced by adjunction units, restriction, tensor and evaluation, hence are natural in both $K$ and $L$. The argument imposed only w-contractibility and the fixed universe conditions; no truncation, finite-generation or dualizability assumption has entered.

Cited nodes: lem-zl-contractible-derived-sections-tensor, sk-thm-pe-weakly-contractible-basis

Source: literature/hemo-richarz-scholbach-constructible-sheaves_arXiv-2305.18131.pdf; Proposition 4.3(1), completion of the internal-Hom comparison by testing on the w-contractible affine basis

