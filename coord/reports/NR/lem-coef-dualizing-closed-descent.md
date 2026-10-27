# Stage-1 report: lem-coef-dualizing-closed-descent

## Files written

- dag/nodes/sec-six-functors/lem-coef-dualizing-closed-descent.json: item, statement, nine-step split; no Mathlib match. Statement unchanged.
- citations.json: 17 verbatim statement excerpts, one for every step/node citation.
- report.md: this report.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for closed/coefficient, exceptional and site-comparison notions. There is no project declaration stating every clause. Existing general categorical results do not establish the geometric comparison in this item.

## WANTED

None.

## Corrections and scope

The imported item had no proof. Its statement is retained exactly. The split supplies the independent boundedness audit and the explicit normalized counit calculation that the blueprint application of finite closed-shriek coefficient change leaves implicit. No Lean was written, and no compiler, Lake or build tool was run. All writes are within this item's sandbox. No other node, chapter, unit, repository or launcher file was edited.

## Unfinished work

None for this one-level split. All prerequisites already exist as DAG nodes, whose proofs remain their own items.

## Blueprint and duplicate searches

Read the source paragraph in literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/lem-coef-finite-dualizing.proof.md. Read the chapter and unit records, SETUP's three-level route and GOAL.md. Ran tools/blueprint_refs.py ancestor on the item and search for coefficient closed, closed-shriek and dualizing, and searched the whole DAG for coefficient/site/counit squares. The ancestor remains lem-coef-finite-dualizing. No other blueprint node states this bounded ordinary-etale descent with its specified coefficient square. Reused lem-sfb-etale-proetale-scalar-mate rather than introducing another scalar/site compatibility lemma, and reused the existing closed-site and closed-chart prerequisites for domains.

## Not duplicates

No new nodes were created.

## Mathlib searches

The five new searches are logged in searches.jsonl and preserved verbatim in search-result-0.txt through search-result-4.txt and in the item's mathlib_searches. LeanFinder was tried with two different phrasings. LeanSearch returned scheme-theoretic closed immersion facts, not derived exceptional coefficient change. Loogle returned FullyFaithful.preimageIso and related generic categorical results; read Mathlib/CategoryTheory/Functor/FullyFaithful.lean lines 202-214. These justify the routine lift-inverse argument but do not state this item. The Mathlib grep found pro-etale topology definitions, not the required comparison theorem. Retained the item's historical search records and results unchanged.

## Review by NR

I read delivery-errors B through E in full and checked the actual node statements against the steps, rather than treating their names as evidence. The source for the item is paragraph 3 of the current finite-dualizing proof, which applies finite closed-shriek coefficient change to the Tate input. The proof is marked agent-written because the expanded descent calculation is supplied here. I also read the finite-rings paragraph of det-prop-scalar-six-direct-image.proof.md and the Hom-bijection proof thm-sf-ambient-adjoint-class.proof.md, and Stacks categories.tex, Tag 0B65, label lemma-transformation-between-functors-and-adjoints. That categorical source explains the counit normalization; it is not being cited as an uncited geometric theorem.

Step 1 uses the statements of lem-coef-dualizing-closed-site, lem-sf-flat-model and lem-coef-dualizing-closed-chart. The first explicitly supplies bounded constructible finite-Tor objects at both coefficient stages; the second explicitly includes the etale flat-model variant; the third explicitly states exact termwise closed direct image and cohomology compatibility. Taking a bounded flat representative of N and tensoring it with B proves boundedness of T_Y N directly. Exact i_* then bounds the source of the ambient Hom set. This avoids inferring the needed domains from the comparison being proved and avoids claiming scalar extension preserves all bounded-below complexes.

Step 2 uses lem-sfb-etale-proetale-scalar-mate with J=N and f=i. The required J and T J bounds were established in step 1; i is finite by the closed-chart statement and so quasi-compact and quasi-separated. The canonical-mate and derived-tensor-pullback statements identify beta with the specified direct-image comparison and the scalar-mate lemma's tensor comparison with t inverse. The finite-direct-image statement defines its coefficient maps by the same adjunction transpose. I checked the displayed formula's direction: multiply the scalar-mate formula on the left by i_*(t_Y) and on the right by T(delta_A) t_P. This gives exactly the item's square, not merely an unspecified isomorphism of objects.

Step 3 applies the finite-direct-image theorem to N, whose required bounded constructible finite-Tor condition is explicitly in closed-site. B is cyclic, hence finite, over A. The theorem supplies the site-image coefficient component and naturality. The component at J_A S_P M is obtained by conjugation with alpha_A; the naturality equation is written in the step. Thus the second invertible component is not inferred from a theorem about arbitrary pro-etale inputs.

Step 4 uses closed-site for the finite-Tor hypothesis on S_P M and for alpha and t. The finite-closed-shriek statement gives the isomorphism and its counit-defined transpose under the transported finite exceptional functor. I checked that the input and its scalar extension have bounded-below etale origins, through the displayed kappa maps, before using the relative adjunction. No ambient unbounded pro-etale adjoint is assumed.

Step 5 uses precisely the full faithfulness on D+ in thm-weil-pbc-site-comparison. Both ordinary endpoints were bounded independently in step 1. Lifting the map and its inverse and checking their composites by faithfulness is a direct categorical argument, not a new lemma or a new node.

Step 6 uses the exceptional-counit equation of lem-coef-site-closed-counit-transport at both (A,M) and (B,M_B), the finite-closed-shriek counit identity, and naturality of the canonical direct-image comparison. I verified the former's H and I H boundedness assumptions from step 1. The displayed calculation has the same source and target throughout. The naturality of the B exceptional counit at v=t_P,M explains the inverse v and inverse J_B(v), rather than silently treating coefficient tensor and exceptional inverse image as commuting.

Step 7 only substitutes equations already established in steps 2, 3 and 6 and the naturality of the specified tensor comparison. I checked its cancellation order explicitly: c_K inverse times i_*(T alpha_A) becomes T(i_* alpha_A) times c_Q inverse; the normalized square then yields T(delta_A inverse)c_Q inverse i_*(t_Y)delta_B = t_P S(c_e inverse). This proves the image of the exact ordinary counit equation. It is marked elementary because it is only substitution and cancellation of those already stated equations, not a geometric interchange claim.

Step 8 uses faithfulness only on Hom(i_* T_Y N,M_B), whose endpoints were independently bounded, and the actual ordinary closed adjunction in lem-exc-closed-ambient. Its counit bijection identifies the descended isomorphism with the named b^e, proving the full stated conclusion. Step 9 checks the empty derived category directly, m=n by counit uniqueness, and r=0 without any positive-dimension assumption.

All non-elementary steps have cited nodes with matching hypotheses. No source proof rather than its statement is used as a premise. There is no new node restating a clause, no unsearched new lemma, no proof hidden in an unsplit statement, and no step exceeds 2000 characters. All cited dependencies were checked for a path back to the item; none reaches it. The statement is not disputed. Generic tools outside the item's unit are declared in split_report.tool_uses with their specific purpose. The closed-shriek route is retained and no prohibited source is used.
