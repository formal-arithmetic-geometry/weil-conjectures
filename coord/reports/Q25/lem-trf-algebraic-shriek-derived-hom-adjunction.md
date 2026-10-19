# Q25: lem-trf-algebraic-shriek-derived-hom-adjunction

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-algebraic-shriek-derived-hom-adjunction.json`: statement, split into eight proof steps; no Mathlib match for the full statement.
- `citations.json`: an entry for every step/node citation, quoting the verbatim statement, including all clauses used.
- `searches.jsonl`: actual Q25 search log produced by msearch.py; imported search records are retained in the item.
- `report.md`: this report.

Zero new nodes; zero new Mathlib leaves. The item statement, statement dependencies, source, created provenance, chapter, unit, and inherited blueprint ancestry are unchanged. The proof is repaired to remove the direct dependency that formed the returned cycle. No unit record is written: the item is not the unit's key statement. `prepare.py` is a sandbox-only generation scratch script, not a DAG delivery file.

## Attachments

None. I searched `WeilConjectures/` in the read-only slopmaster2 source by the exact blueprint tag and by coinduction/coextension, derived Hom, double dual and scalar restriction. The project declarations found concern ordinary coextension, sheaf-algebra adjunction, or geometric duality; none states every clause of this internal derived-Hom comparison together with the scalar-to-bidual evaluation identity. No sorry declaration is treated as finished.

## WANTED

None. All sources used are in the shared literature checkout.

## Repair of returned delivery

The landing was rejected because the item and `lem-trf-derived-coinduction-adjunction` depended on each other. I re-read the current coinduction node and removed it from this item's `proof_deps` and Step 1 `uses`. Step 1 now constructs the K-injective coinduced Hom complex directly from `def-pur-derived-internal-hom`; no other dependency changed. The citation manifest was updated by removing the corresponding Step 1 quote.

## Problems found and changes

The item was statement-only. The Stacks 0BZW display suppresses the internal coinduction adjunction and its map normalization. Merely identifying its two derived Hom objects would not prove that the scalar-action map is canonical biduality. Steps 2–4 supply the actual comparison; steps 5–8 check the actual scalar morphism, all shifts, and its bidual normalization. No hypothesis is added and no assertion of bidual invertibility is made.

The inherited item has eight older Mathlib search records from its creation, including one explicitly mis-scoped grep and one Loogle query with an unknown identifier. I preserved those records as instructed, read their recorded results, and supplied six real Q25 searches with the unchanged full statement in mind. They find the ordinary restriction/coextension Hom equivalence and evaluation counit, not the full unbounded derived-Hom assertion. I read Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:441–680, including `HomEquiv.fromRestriction`, `HomEquiv.toRestriction`, the counit, and `restrictCoextendScalarsAdj`, and DerivedCategory/KInjective.lean:43–90 for the generic K-injective localization infrastructure. The existing DAG already has the generic K-injective Hom bijection, so no replacement Mathlib node is created.

The source main-20261015 blueprint proof of lem-trf-local-term-locality, clauses (1)–(2), keeps the contracting-correspondence/normal-cone specialization route. The inherited via chain reaches this item through the relative-duality polynomial chart and algebraic-shriek-relative-perfect. I read that parent, whose step 4 is the direct consumer: it needs precisely the evaluation-normalized comparison proved here. This split does not change the chapter or unit route. Generic tools outside this unit are explicitly declared in split_report.tool_uses. The coinduced Hom complex is constructed directly in Step 1, so the item no longer depends on the separately split coinduction-adjunction node.

## Not duplicates

No new nodes are created. The DAG and whole-blueprint searches for coinduction, scalar evaluation, 0A70/0A71/0BZW, and internal-Hom scalar restriction found `lem-trf-derived-coinduction-adjunction`, `lem-trf-perfect-algebra-coinduction-tensor` (requires a perfect algebra and gives a tensor formula), and `lem-sfb-dc-hom-scalar-adjunction` (derived extension in the first Hom variable). The coinduction node is a separate downstream consumer after the earlier delivery and cannot be cited here without a cycle, so Step 1 now gives the K-injective Hom construction directly from `def-pur-derived-internal-hom`. The last two are different from this coinduction-in-the-second-variable statement and are not used as substitutes. Existing duality-map and Hom/tensor model nodes supply the other tools. Blueprint search found no same-statement blueprint node, so same_as remains empty.

## Review by Q25

I read dualizing.tex, Tags 0A70 (lemma-right-adjoint), 0A71 (lemma-RHom-ext), and 0BZW (lemma-relative-dualizing-algebraic), especially the display proving (1)(c). I also read sites-cohomology.tex, lemma-compose 0A90, lemma-RHom-into-K-injective 0A94, lemma-RHom-well-defined 0A95, lemma-internal-hom-evaluate 0A97, and lemma-dual 08JD/its 08JE equation; and the ordinary-module currying proof in more-algebra.tex, lemma-compose 0A5Y, remark-internal-hom 0GWQ, and section-RHom 0A5W. The one-object site has only the identity covering, so its module sheaves and internal Hom are the ordinary module versions, with identity global sections. No pro-etale, completed, rational, or infinity-categorical coefficient category is substituted.

For the repaired Step 1 I opened `def-pur-derived-internal-hom` and the Stacks 0A70/0A71 construction: it supplies a K-injective representative, the Hom complex, its choice independence, and the derived Hom interpretation. I wrote the coinduced complex directly as `J = Hom_P(A[0], I)` with right-multiplication action and recorded evaluation at 1 as the counit candidate. This avoids importing the downstream coinduction node and removes the cycle.

For Step 2 the cited Hom-complex definition gives the product terms and the differential d(f)=d_target f−(−1)^r f d_source. I checked P-linearity, A-linearity of the inverse, both inverse identities and that exact differential equation. The same formula works for degree −1 cochains, which is needed in the next step. This is a direct calculation, not a new hidden lemma.

For Step 3 the cited K-injective definition is null homotopy for every map from an acyclic complex. Restriction leaves cohomology unchanged, so the transpose is a map from an acyclic P-complex. Its null homotopy transposes back by the explicit degree −1 inverse. This proves K-injectivity in three lines; it is elementary from Step 2 and the definition, and is kept as a step rather than a node. It never asserts that restriction preserves K-injectivity.

For Step 4 the K-injective targets needed by `lem-pur-rhom-well-defined` are I over P and J over A, the latter proved in Step 3. That node really permits arbitrary unbounded source quasi-isomorphisms. `lem-weil-pbc-kinjective-hom-derived` really gives the full unbounded Hom bijection and uniqueness up to homotopy, not just bounded-below maps. I checked that the explicitly defined Hom construction carries target homotopies degreewise and that all resolution comparison maps commute with evaluation. Thus the naturality is for derived arrows, not just maps of chosen complexes.

For Step 5 I checked the shift definition in `def-weil-abstract-derived-category` and computed the degree-r simultaneous-shift sign (−1)^(nr). Multiplying the shifted Hom differential by that sign commutes with d because (−1)^(n(r+1)+n)=(−1)^(nr). Scalar maps have degree zero and acquire no sign. Coinduction of I[n] is V[n] because A lies in degree zero. K-injectivity of the shifts is obtained by the explicit shifted null-homotopy argument from its cited definition.

For Step 6 the Hom differential and K-injective Hom model cited there make the scalar action an actual chain map with the correct target. I computed (a h)(1)=h(a), with no sign. This is equality of maps, not just equality of objects or an assertion that an isomorphism transports the desired map.

For Step 7 I checked the statement of each cited resolution and tensor node. `lem-pc-kflat-resolution` provides K-flat complexes with flat terms and actual quasi-isomorphisms onto A[0] and UV; `lem-weil-pbc-site-derived-tensor-descent` computes their unbounded total tensor. `lem-pur-rhom-well-defined` applies to r:F→A with the identical K-injective target I. `lem-pur-hom-kflat-into-kinjective` says exactly that Hom(F,I), and later Hom(T,I), are K-injective. I added this citation during self-review: without it the chain currying argument would conceal the justification for its derived Hom bijection. `lem-sc-derived-hom-tensor-total` provides the functorial total-Hom/tensor isomorphism; its explicit currying formula was checked against the source differential. `lem-weil-pbc-kinjective-hom-derived` then identifies the homotopy classes with derived morphisms. Finally the cited duality-map statement defines b_A as the transpose of braided coefficient evaluation. I use that unconditional construction, not its optional representative-normalization clause whose extra hypotheses need not hold here.

For Step 8 I checked that currying delta on F and T gives t(z)(r(x)), while exchanged evaluation gives (−1)^(|x||z|) times that. If x has nonzero degree, r(x)=0 since A[0] is in degree zero; otherwise the sign is 1. Thus the maps agree on every homogeneous summand, including unbounded ones. The cited K-flat tensor, chain currying, K-injective Hom and canonical-bidual statements say exactly what this comparison uses. I explicitly included Hom(F,I) and Hom(T,I) K-injectivity in the final argument so that the derived transposition really is bijective.

I checked B–E of delivery-errors against the final files: no new statement-only node to restate a clause, no copied proof hidden in a statement, no unintroduced objects or changed hypotheses, no source/tag-only non-elementary citation, no appeal to a cited node's proof, no reversed adjunction, and no SGA citation. Every cited node's statement was read. The citation manifest uses exact statement text for every step citation. All eight steps are below 2000 characters; the longest is the explicit resolution-level evaluation comparison, and it does not hide a new smaller claim. The K-injective preservation argument is elementary and fully written out, so creating a separate node for it would violate the elementary-node rule.

Edge checks: if P=A the comparison is the identity and evaluation is the ordinary scalar identity. If A is the zero ring all A-complexes and the two sides are zero. If X=0 or Y=0 the same formulas give zero. For the nonflat map Z→Z/2, the complex RHom_Z(Z/2,Z) has its Ext term, and the proof uses a K-injective target rather than incorrectly replacing it by ordinary Hom_Z(Z/2,Z)=0. Shifts n=1 and n=−1 leave degree-zero scalar multiplication unchanged. For a field P and an infinite-dimensional algebra A such as P[t], the bidual evaluation need not be an isomorphism; this statement only identifies that map, so it imposes no hidden perfectness assumption. No finiteness assumption is used in the product-total Hom adjunction.

## Unfinished work

None for the requested one-level split. The existing cited nodes retain their own statuses and future splitting obligations; this delivery does not claim that the entire dependency closure is finished. Required server dry run and push are run after this report is written.
