# Stage-1 repair: lem-coef-rigidification-identity-action

## Files written

- `dag/nodes/sec-six-functors/lem-coef-rigidification-identity-action.json`: four-step repaired split, including an explicit normalization of its point map.
- `dag/nodes/sec-six-functors/lem-coef-point-family-q-counit-identification.json`: one new statement-only, unsplit supporting node; no Mathlib match.

`citations.json` and `searches.jsonl` are sandbox verification artifacts, not files included in the delivery commit. The inherited command-generated search records and the item's prior search metadata are retained.

## Attachments

None. Searches of the read-only source projects under WeilConjectures for the blueprint tag, rigidification, identity-action and pinched-resolution vocabulary found no exact sorry-free project declaration. The master source is reference material, not evidence of a finished proof.

## WANTED

WANTED: an archival extract of Lurie, Higher Topos Theory, Sections 2.2.2 and 2.2.4 (opening comparison before Proposition 2.2.4.1, printed p. 88), and Section 5.1.3 (the singular-realization enriched Hom construction), for this item and the new node. I read the p. 88 comparison online; it identifies the composite into the enriched Hom with the Q-evaluation counit.

WANTED: archival Kerodon extracts of 06QR (Example 4.6.7.7), 01LF (Remark 4.6.7.6), and 038A (Definition 5.6.6.1), for the canonical enriched mapping comparison and evaluation at the chosen point. I read these online. The right-pinched maximum/prism and constant-diagram formula in the new node is an agent formulation of these comparisons, rather than a verbatim assertion of one source. No Stacks tag states this specialized homotopical comparison. The item proof remains marked agent-written.

## Returned point 1: Q-counit identification and normalization

The inherited Step 1's calculation and its citations are retained: on each Q-summand the explicit enriched action evaluated at the singular identity is exactly u theta. The original Step 2 was not justified by the statements it cited. The point-cocone criterion supplies an equivalence without specifying the Q-counit normalization; the pinch comparison supplies only the map into the arrow space. I corrected this by introducing the new node and deriving the required equation from its explicit alpha, beta and E formulas.

STATEMENT-DISPUTED: the original expression “under the constant-diagram equivalence” leaves the point map's normalization unspecified. A bare existence statement does not fix its homotopy class: for K=Delta^0 and the discrete two-point Kan complex Y, postcomposing an equivalence with the transposition changes its corresponding point. The source's intended comparison is the canonical enriched one, whose inverse appears explicitly in Kerodon 038A. The item now specifies beta from the new node and [e_x]=[beta_{*,H(x)}]^{-1}[gamma_x]. This corrects that ambiguity without adding hypotheses or weakening the asserted equality or weak-equivalence conclusion. Both current consumers require this canonical identity-action map: lem-coef-infinity-pointwise-yoneda-evaluation and lem-coef-infinity-hom-bifunctor-functoriality.

The new node is independent of the concrete representable H. For arbitrary Kan X,Y it identifies R=Map^R_S(X,Y) with Sing_Q Fun(X,Y), identifies E with the enriched counit composed with theta, defines alpha using the maximum map q:Q→Delta, and beta=j alpha. It states E=alpha^{-1}p_R in the localization and compatibility with enriched composition and evaluation at a point, including the prism reparametrization and all parameters. Currying beta specifies the point-family equivalence. It asserts no weak equivalence of the item's identity-action map and contains no proof steps.

For its later split, the intended independent argument is: R=Sing_Q(T) by the explicit enriched adjunction, and E V(alpha)=q_T on summands. The pointwise maximum of p and q gives natural homotopies p~max(p,q)~q. Naturality of p and cancellation then give E=alpha^{-1}p_R. The three-layer subset-poset prism compares enriched composition with coherent edge composition; setting its first arrow to eta gives evaluation at eta. All formulas commute with parameter operators, and currying gives the constant-diagram comparison. This guidance is in the report, not a proof hidden inside the child statement.

## Returned point 2: saturation without a cycle

The converse use of lem-cbc-kan-whitehead-inverse is removed. I opened both suggested replacement nodes. Their statements supply exactly model-category saturation and the Kan-Quillen structure, but the current dependency graph makes the first citation circular:

lem-coef-model-localization-detects-weak-equivalences → lem-coef-model-infinity-derived-adjunction → lem-coef-cosimplicial-frame-mapping → lem-coef-hammock-infinity-localization → lem-coef-infinity-functor-pushout → lem-coef-cat-infinity-colimits-cartesian-closure → lem-coef-infinity-pointwise-adjoint-criterion → lem-coef-infinity-pointwise-yoneda-evaluation → this item.

I repaired the inference independently using lem-cbc-realization-weak-equivalence. For each Kan Z, the contravariant ordinary functor B↦pi_0^e Fun(B,Z) sends every weak equivalence to a bijection by its forward implication, so it factors through the formal localization. Invertibility of [e_x] therefore gives bijections on all these tests; the converse implication proves that e_x is a weak homotopy equivalence. This is a complete saturation argument using an existing independent statement. It needs no new saturation node and avoids the cycle. The Kan-model-structure node is consequently unnecessary in the final dependency list.

## Review by Q36

I read the fixed chapter and unit records, the current main-20261015 ancestor paragraph (the derived coefficient-adjunction calculation), both direct consumers, the item, the new node, and every statement cited by the final four steps. The retained sandbox item was compared with the shared copy; its proof work and search evidence are retained and the only statement clarification is the normalization recorded above. No target, definition, chapter or unit route is changed; no geometric coefficient categories or base-change morphisms occur in this foundational simplicial item. No SGA source is used.

Step 1 uses def-cbc-enhanced-diagrams-cones for right-pinched parameters, def-coef-infinity-category-of-spaces for the explicit postcomposition action and singular identity, and lem-coef-pinched-rigidification-resolution for theta's actual Q-summand formula. The unit law and naturality give b_x=u theta on each summand and on the coend. This was the correctly justified step of the returned split and is retained.

Step 2 puts X=H(a), Y=H(x) and h=Map^R(H). The naturality clause of lem-coef-infinity-pinch-comparison supplies the H-image prism jh. The new node supplies evaluation compatibility and the exact counit formula E=alpha^{-1}p_R. These give e=ev_eta alpha^{-1}h, then naturality of p gives e p_M=ev_eta E V(h). The new node's summand formula identifies the latter with precisely the enriched action at eta computed in Step 1. Each cited statement says the fact taken from it; the arbitrary existence of a point-family equivalence is no longer used for that identification.

Step 3 uses the two specified weak equivalences from the pinched-resolution statement and the arbitrary-simplicial-set singular unit to make [e_x] invertible. The forward and converse clauses of the realization criterion supply exactly the two Kan-test implications in the saturation argument above. The definition of formal localization, introduced in the item, supplies the factorization universal property. No inverse Whitehead implication or Kan hypothesis is silently imported.

Step 4 uses naturality of p, theta, the pinch map, enriched postcomposition, the singular unit, and the new node's alpha,beta,E comparisons. It retains the coend operators and proves the universe clause by reinterpreting the same underlying simplicial maps and realization tests. The def-cbc tool_use now claims only notions that its statement actually defines; it no longer attributes formal-localization notation to that node. The singular-unit and realization-criterion nodes are declared off-unit generic tools with their exact uses.

Small cases checked: M_x empty; M_x=Delta^0; Q^0=Delta^0; discrete two-point targets (which expose the normalization issue); and degree-one face/degeneracy maps. For the new node, an empty enriched Hom gives empty R and empty coends; X=Y=* gives the identity comparison. Evaluation at eta is used only when the stated point exists, so no point of an empty X is chosen. The maximum formula is natural under monotone maps, including repeated vertices. No connectedness or nonemptiness hypothesis is added. All four proof steps are below 2000 characters. Exact statement quotations for every cited node in every step are present in citations.json.

I checked delivery-errors B–E: the child has a self-contained TeX statement, explicit notions and blueprint ancestry, empty proof/proof_deps and null proof_origin; no elementary node or item clause is introduced. Its via is the item followed by the item's full inherited chain. The whole DAG and blueprint were searched for the comparison, Q-counit and point-family terms, and the source projects were checked for an attachment. New searches used two semantic phrasings plus Loogle and grep through msearch.py; the final child copies the seven actual generated records. Mathlib/SimplicialNerve.lean:14–35 supplies the nerve construction and lists the locally Kan comparison as future work; SimplicialCategory/Basic.lean:65–67 only identifies vertices. Neither supplies the full-parameter counit formula. A mistaken early invocation placed search output under proposed helper ids; those outputs are not used as this item's generated log. Subsequent required searches were run with the correct Q36/item arguments. No unrun search is recorded.

## Not duplicates

lem-coef-point-family-q-counit-identification vs lem-coef-rigidification-identity-action: the child is the concrete Kan-nerve mapping/counit normalization for arbitrary X,Y, with no quasicategory C, rigidification representable H or weak-equivalence conclusion for e_x. The item computes H's action on the identity and derives that conclusion by applying the comparison and resolution theorems.

lem-coef-point-family-q-counit-identification vs lem-coef-space-point-cocone-criterion: the existing statement characterizes colimiting point cocones through an unspecified family-of-points equivalence; it does not state the alpha,beta,E formulas needed here. The child supplies their normalization and reparametrization, without restating the colimit criterion.

lem-coef-point-family-q-counit-identification vs lem-coef-pinched-rigidification-resolution: the existing statement gives Q,V,p,theta and the evaluation counit's weak equivalence. It does not identify the constant-diagram point-family equivalence with that counit. The child supplies the specific coherent-nerve comparison.

lem-coef-point-family-q-counit-identification vs lem-coef-coherent-nerve-comparison: the global Bergner/Joyal theorem has an abstract mapping comparison, but no explicit maximum/prism and point-family Q-counit formula. Its infrastructure depends back on this item's identity-action foundation, so it cannot be invoked here. The child isolates the independent Kan mapping calculation needed below the global result.

lem-coef-point-family-q-counit-identification vs lem-coef-infinity-hom-bifunctor-functoriality: that node constructs Hom bifunctors on arbitrary quasicategories and uses this item; it is not an independent Kan-nerve counit normalization.

## Retained earlier attempt and remaining work

The returned sandbox originally split the item into the same four tasks: Q-summand action, point-family identification, weak-equivalence detection, and naturality. The original report incorrectly certified the middle two; this repair replaces those arguments and preserves the first and final tasks, inherited source citations, blueprint ancestry, item search metadata and the original five command-generated search records. The original source-archiving WANTED requests remain above. There was no independent second reading in the earlier worker attempt; the audit is appended below.

Only the new supporting child remains unsplit, as required by the one-level contract. No Lean is written or compiled, and no push is attempted. The required dry-run checks are run with deliver.py --no-push; the successful sandbox is left for the independent second reader.

## Same-source-tag duplicate audit

lem-coef-point-family-q-counit-identification vs lem-coef-infinity-pointwise-yoneda-evaluation: the existing theorem evaluates full coherent transformation spaces from a representable and constructs small models. It depends on this item; it does not state the independent alpha,beta,E mapping/counit normalization. Both cite Kerodon 038A for different parts of that construction.

lem-coef-point-family-q-counit-identification vs lem-weil-pbc-affine-galois-base-change-fiber-transitivity: that node concerns the action of a possibly infinite Galois group on points of an affine scheme after field base change. Its Stacks tag 038A and the child's Kerodon identifier 038A belong to different catalogs; the statements have no mathematical overlap.

lem-coef-point-family-q-counit-identification vs lem-weil-pbc-galois-base-change-fiber-transitivity: that node is Galois transitivity on geometric base-change fibers for arbitrary schemes. Its Stacks tag 038A is unrelated to Kerodon 038A, which defines corepresentable functors. I opened both transitivity statements during the tag audit; neither concerns simplicial mapping spaces or a Q-counit.

## Second reading by Q36

- Step 1: checked the explicit H-action, singular identity, Q-summand formula, and coend relations against `def-coef-infinity-category-of-spaces`, `def-cbc-enhanced-diagrams-cones`, and `lem-coef-pinched-rigidification-resolution`; PASS, with the displayed map computed on every summand.
- Step 2: checked the X,Y,R,T,h substitutions, naturality of the pinch map, the normalized β comparison, and the E=alpha^{-1}p_R counit equation against the cited node statements; PASS, and the action map is identified on all (Q^n)-summands rather than only vertices.
- Step 3: checked the two weak-equivalence inputs, the singular-realization unit, and the Kan-target test criterion including empty cases; PASS, with the localization saturation argument written explicitly and no circular Whitehead dependency.
- Step 4: checked naturality in (C,a,x), coend face and degeneracy compatibility, and universe enlargement against the cited naturality clauses; PASS, with no extra hypotheses.
- New node `lem-coef-point-family-q-counit-identification`: checked every definition, hypothesis, maximum-map formula, alpha,beta,E comparison, composition/evaluation compatibility, and constant-diagram specialization against the stated HTT/Kerodon source places and all five statement dependencies; PASS as a statement-only supporting comparison, not a restatement of the item.
- Small cases checked: M_x empty, M_x = Delta^0, Q^0 = Delta^0, X = Y = *, an empty enriched Hom, discrete two-point targets, and degree-one faces/degeneracies. The discrete two-point case confirms that an unspecified point-family equivalence would permit a transposition, so the repaired β normalization is necessary.
- Repair: corrected the item node's `created.item` provenance from the unrelated `lem-coef-infinity-pointwise-yoneda-evaluation` to `lem-coef-rigidification-identity-action`; no mathematical statement or proof step was otherwise changed.
