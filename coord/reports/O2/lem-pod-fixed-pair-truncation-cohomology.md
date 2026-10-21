# Worker report: lem-pod-fixed-pair-truncation-cohomology

## Files written

- `dag/nodes/sec-poincare-duality/lem-pod-fixed-pair-truncation-cohomology.json`: statement, split into ten steps; Mathlib searches find infrastructure only, not this fixed-pair assertion.
- `citations.json`: 26 step/node citations, each with a contiguous verbatim extract of the cited statement.
- `report.md`: this report. No new nodes and no new Mathlib leaves.

## Attachments

None. I searched `lean/WeilConjectures/` by the exact blueprint tag and by truncation, fixed-pair, Weil-complex and cohomology terminology. The exact item tag is absent. `SixFunctors/ProEtale/Adic/Truncation.lean` proves underlying truncation assertions, not the rational/common-stage pair lifts, third-arrow equivariance and point-transport equation together. Its implementation note also distinguishes its concrete adic coefficient category from the rationalized stage. `WeilSheaf/FieldCoefficient.lean` uses a derived category of Weil sheaves, whose morphisms include derived Weil extensions, whereas this item uses pairs in the underlying derived category. `SixFunctors/ProEtale/FiniteCoefficient/Derived/WeilComplex.lean` defines strict pairs at finite coefficients, not the two coefficient stages of this item. None is an exact attachment for this item. No compiler was run.

## Wanted sources

None. The current blueprint, BBD PDF and all cited DAG statements are available locally.

## What changed and what was wrong

The live item was unsplit with an empty proof. Its statement is retained word for word. The current ancestor is `prop-weil-operations`, current blueprint proof sentence 2, with the cohomology conclusion in the ancestor's statement. I read `dag/chapters/sec-poincare-duality.json`, `dag/units/sk-lem-finite.json`, the three-level route rules, and the current blueprint proof. This is an auxiliary node, not the unit's key statement, so no unit realization fields are changed.

The important gaps to avoid were treating commutation of the two functors as proof of equivariance of the third triangle arrow, and treating the definition of point transport as proof of its naturality. Steps 5–6 use uniqueness of the entire truncation triangle, with the shift comparison displayed, and Step 9 cites the existing theorem that actually states naturality. I also name the existing definitions of ordinary and compact-support direct image and of derived cohomology in `stmt_deps`, because the conditional last clause uses those notions. No hypothesis or conclusion was changed.

The proof is marked agent-written: the blueprint's one-sentence truncation argument is expanded into actual pair calculations using BBD 1.3.3 and 1.3.4 and the existing DAG interfaces. No SGA source is used. For the abstract t-structure result there is no Stacks counterpart in the claimed generality; the cited node explains the distinction from Tags 0118 and 08J5. I use BBD rather than falsely assigning a Stacks tag.

## Not duplicates

No new nodes were created. Whole-DAG searches and `tools/blueprint_refs.py search` for truncation, t-exactness, truncation triangles, Weil pairs and point transport found the existing nodes used here. In particular `lem-pod-texact-truncation-comparison`, `lem-weil-heart-short-exact-triangles` and `lem-weil-frobenius-point-transport-natural` supply the generic facts; no new node relabels a clause of the item. The item's `blueprint.from` already names the correct ancestor and place, and no other blueprint node states the whole item, so `same_as` stays empty.

## Review by O2

I read delivery-errors B–E, including the full repeated B–E checklist, against the item and each cited statement. I read the current `prop-weil-operations.proof.md` second sentence and its ancestor statement as the source of the item; I also read BBD Proposition 1.3.3(i),(ii) and paragraph 1.3.4 on printed pages 29–30 (PDF pages 30–31). BBD explicitly includes uniqueness of the degree-one arrow, not just the first two objects. There are no new-node sources to review.

For Step 1 I opened `prop-constructible-truncations`, which explicitly supplies the bounded t-structure and automorphism commutation at both field stages. I opened `lem-pod-semilinear-field-operation-lifts`, whose first paragraph explicitly says that the semilinear Frobenius pullbacks are exact equivalences at the rational/common stages. I only take that assertion; I do not use its later operation-lifting conclusions. Its separated-finite-type morphism hypothesis is met by choosing the identity of W_0; this adds no separatedness assumption on W_0. Preservation of the t-structure halves is checked by truncating an object already in the half. The resulting functor meets all the hypotheses of `lem-pod-texact-truncation-comparison`, whose statement gives natural isomorphisms with exactly the counit/unit characterizations used here.

Steps 2 and 3 use that natural comparison and the actual fixed-pair equation in `def-weil-weil-sheaf-complex`. The displayed chains verify morphism equivariance, rather than presuming a functor lift exists. Composition and identities follow from those of the underlying truncation functors. The upper and lower canonical-map equations are written separately, with their opposite comparison characterizations respected.

Step 4 uses the shift comparison supplied with the exact functor P in `lem-pod-semilinear-field-operation-lifts` and the fixed-pair definition. Its displayed equation checks the arrow rule for every integer shift. Step 5 applies clause (1) of `lem-weil-heart-short-exact-triangles`: the P-image triangle is distinguished because P is exact, and its outside terms lie in the required halves because P is t-exact. Its comparison over the identity of PK is uniquely determined; the characterization in `lem-pod-texact-truncation-comparison` identifies its outer components with the chosen c-minus and c-plus. The displayed last square includes s_{U,1}P(delta), which cannot be replaced by P(delta) with the wrong target.

Step 6 applies the same uniqueness assertion to the isomorphism theta_K of middle objects. The cited statement's adjunctions identify the outer components as the truncations of theta_K. Combining the two displayed last-square equations yields delta_K theta_V = theta_{U[1]} P(delta_K) with exactly Step 4's structure, including the shift. This is a direct application of the existing uniqueness theorem, not a hidden new lemma.

Step 7 composes the two proved truncation lifts and the proved shift lift. I checked the domains of c-plus at tau-less-equal K, tau-greater-equal applied to c-minus, and the shift comparison: their composite has source P H^i(K) and target H^i(PK). The cohomology expression and heart membership are those of `prop-constructible-truncations`. The forgetful assertion is the object/arrow prescription of `def-weil-weil-sheaf-complex`.

Step 8 also handles the standard successive-truncation forms: applying the already proved triangle argument to tau-less-equal-m K at m-1 produces the cohomology quotient. The absorption identification is uniquely characterized by the upper counit, so equality of its Frobenius composites can be checked there; the lower version uses the unit instead. BBD 1.3.4 gives these absorption identifications, and the cited node's truncation adjunctions give their uniqueness. This step uses the previous arrow equations and does not assume that any arbitrary cone in a category of pairs is a distinguished triangle.

For Step 9 I opened `def-weil-frobenius-point-transport`, which explicitly defers naturality to its separate theorem. I then opened `lem-weil-frobenius-point-transport-natural`, whose clause (2) states the exact naturality equation for every derived morphism at E and at the common stage, including coefficient-extension compatibility. The displayed four-term chain uses that equation and the fixed-pair arrow equation. Finally, `def-weil-abstract-derived-category` explicitly defines the cohomology functors by localization, so applying H^i to that equality preserves both composites. The ordinary/compact-support clause remains conditional on an already supplied bounded-constructible Weil lift; no separatedness or preservation theorem for extra domains is inserted.

Step 10 checks the scope: all three actual interfaces (bounded t-structure, exact P, natural point transport) explicitly cover the rational and common-stage categories, so the proof works inside each category directly. In particular I did not assume that a common-stage arrow already exists over the initial E. The triangles are always in the underlying category; no triangulated structure on pairs is used.

I checked the zero complex, a single sheaf in degree j with cutoffs below/at/above j, zero and identity Weil morphisms, integer shifts including negative i, and the point with trivial or nontrivial invertible Frobenius. In the single-degree case truncations are respectively zero or the original pair and all boundary equations reduce to zero; on a point the final equation is the usual intertwining equation. The adjunction arguments in Steps 5–6 require the outside degree bounds, which are explicitly verified. The scheme automorphism is geometric semilinear Frobenius, not absolute Frobenius or a presumed k-linear map. The non-elementary steps are all under 2000 characters; no long step conceals a comparison lemma. The 26 quotes are taken from statements, not proofs. All required Mathlib searches were run through msearch.py; both semantic phrasings and the source hits were read, and the saved queries are copied exactly from searches.jsonl. No unperformed search is reported.

## Tool uses

- `lem-weil-heart-short-exact-triangles`, clause (1): a generic uniqueness/adjunction tool for the underlying t-structure, used to identify the full truncation triangle including its boundary. It does not change the unit route.
- `lem-weil-frobenius-point-transport-natural`, clause (2): the generic naturality theorem for the precise point transport; the definition does not assert it. It does not replace a finiteness step of the unit.

These are declared in `split_report.tool_uses`; maintainer-owned `tool_uses` is not edited.

## Unfinished work

None in the one-level split. Existing cited nodes retain their own independent statuses. Delivery validation and push are performed through the prescribed delivery tool; no local check_dag, review_split, preflight, Lean, Lake, or build was run.
