# Stage-1 delivery: lem-pur-projection-comparison-etale-origin

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-projection-comparison-etale-origin.json`: statement, split; seven proof steps, no Mathlib match. The statement and its statement dependencies are unchanged. All comparisons retain their specified direction and fixed-compactification normalization.
- `citations.json`: 21 verbatim statement excerpts, one for each cited node in each proof step.
- `report.md`: this report. `searches.jsonl` contains the actual Q92 search runs; `write_split.py` is sandbox scratch work, not a delivered node.

## New nodes

None. Zero new nodes and zero Mathlib leaves. The needed proper coherence, lower Tor bound, and open full-faithfulness results already have nodes. The open square itself is a short calculation using their statements, not an added lemma.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, projection/comparison, etale origin, and the pertinent derived projection modules. `AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarProjectionMap_app_app_leftDerived` in `SixFunctors/ProEtale/Derived/LowerStarProjectionComparison.lean` proves transfer of invertibility of the proper projection map, not the equality of the named compactification projection maps with the specified C. `hasProjectionFormulaOfCompactification_of_comparison` in `ProEtale/Derived/ProjectionFormula.lean` is likewise an invertibility result. Neither gives this item's every clause, so neither is an attachment. The item has no recorded Lean declaration or audit frontier to attach. The read-only upstream master is not used as proof evidence.

## WANTED

None. All sources used are available locally. No download, compiler, Lake, or Lean modification was made.

## What was wrong or missing

The existing item had its full statement but no proof. It is a legitimate smaller coherence obligation extracted from `thm-pur-cohomological-smoothness`; no statement correction is required. The parent source is the current main-20261015 proof, first paragraph, “Because the map is obtained by transposing the projection formula and counit on both sites”. I checked the chapter `sec-smooth-purity` and the bound unit `sk-prop-cohsm`; this split supplies that transport calculation and does not change the orientation-free cohomological-smoothness route, the chapter, or the unit record.

A tempting existing result, `lem-pur-finite-ring-site-tensor-transpose`, has the compact projection compatibility as clause 2 but assumes X and Y separated over k. This item's schemes need not be absolutely separated. I did not apply it by silently strengthening the hypotheses. The general ringed-topos projection/exchange lemma and open-adjunction calculation apply to the actual hypotheses.

Similarly, `lem-pur-open-projection-site-transport` imposes a shifted locally free finite-rank first factor. It cannot be applied to arbitrary bounded constructible M. Its existence was checked in the duplicate search, but the split instead uses the general open normalization and the ordinary etale derived tensor identity, then checks the two restricted maps explicitly. No new near-duplicate was introduced.

The Tor assumption is on H alone. In particular boundedness of M is never treated as finite Tor amplitude. It suffices to keep Q and D bounded below, which is all the canonical-mate comparison requires. No constructibility-preservation theorem or unbounded comparison result is smuggled into this typing check.

## Searches and non-duplicates

Read the whole DAG statements of the possible comparison nodes, including `lem-weil-boundary-proetale-projection-comparison` (closed immersions only), `lem-pur-finite-ring-site-tensor-transpose` (absolute separatedness and an unbounded exceptional-adjoint package), `lem-pur-open-projection-site-transport` (shifted locally free first factor), `lem-sf-pf-coefficient-realization-transport` (conditional primitive compatibility data), and `lem-sf-pf-compactification-pasting` (a scheme base-change square). None is used outside its hypotheses. No new node is needed.

Ran `tools/blueprint_refs.py ancestor` and whole-blueprint searches for projection, 0E48, open tensor, projection comparison and projection comparison etale origin, and searched the DAG for the same notions and source tags. The nearest ancestor remains `thm-pur-cohomological-smoothness`, and `same_as=[]` is retained: the general projection-formula blueprint nodes assert invertibility, rather than this specified map equality. The ancestry place was already explicit and is retained.

Ran Q92 msearch with the exact five queries recorded in the item and `searches.jsonl`: leanfinder twice, loogle, grep, and leansearch. All services responded. Read the hits: monoidal adjunction constructions and their counit equations, exponentiable-morphism pushforward identities, ordinary sheaf pushforward counits, product projections, algebraic etale topology and condensed module lemmas. None states this equality of derived compact-support maps. The second semantic phrasing asked for direct-image mate compatibility with a tensor projection morphism; it too gives only different categorical counit identities. The inherited Q39 searches are retained verbatim, and the five actual Q92 runs are appended, without inventing results.

## Tool uses

`split_report.tool_uses` declares the generic off-unit results used for the Tor-domain check, the ringed-topos projection square, comparison maps, and the open normalization. In particular `lem-pur-compact-support-site-coherence` is used solely for its explicitly displayed formula for B at a chosen compactification. No refinement, composition or exceptional-adjoint theorem from it replaces any step of this unit. No maintainer-owned top-level `tool_uses` field is set.

## Review by Q92

I read the current blueprint proof named above and the local Stacks sources, not just their tag summaries: sites-cohomology.tex 0E48 (`remark-compatible-with-diagram`), 07A4 (`lemma-pullback-tensor-product`), 0F1M (`lemma-bounded-below-tor-amplitude`) and 0GL1 (`lemma-j-shriek-and-tensor`); proetale.tex 09AF (`lemma-jshriek-comparison`); and sites-modules.tex 0E8I (`lemma-j-shriek-and-tensor`). 0E48 explicitly concerns a commutative diagram of ringed topoi, without a Cartesian hypothesis. Its proof is omitted there, so the split uses the existing node that states this precise coherence, rather than pretending the tag supplies an unrecorded proof. 09AF constructs the open comparison by adjunction, and 0GL1 constructs the derived tensor identity using a K-flat model of the ambient tensor factor. This is the normalization used in the open-square calculation. The proof origin is marked agent because it expands the blueprint's transport sentence into this particular composition calculation.

For Step 1 I opened the coefficient definition, proper-basic, 0F1M node, exact etale extension, and lower tensor-bound node. The coefficient definition actually asserts finiteness of A, proper-basic actually supplies both qc and qs, and the K-flat model node includes pullback stability. The lower tensor-bound node requires a lower Tor bound, which I check by pulling back the model and testing it against degree-zero sheaves. Thus its hypothesis holds for p*H and f*H; bounded M supplies the other lower cohomological bound. This proves E, Q and j!D are in D+ under exactly the item's assumptions. M need not be perfect.

For Step 2 I checked the statements of the ringed-topos tensor comparison and comparison-pullback node. They provide precisely the tensor isomorphisms and the canonical inverse-image comparison. The additional coherence written in the step is a direct pure-tensor calculation in their K-flat models: both composites act identically in each bidegree and have the same Koszul differential. This fixes all the suppressed tensor identifications, including the direction of t.

For Step 3 I opened the canonical-mate node and the ringed exchange/tensor coherence node, and compared their definitions of the mate. The latter uses theta from the pro-etale pullback composite to the etale pullback composite; with the site's square, theta is a inverse. The canonical-mate node defines exactly its transpose and asserts invertibility for finite coefficients, qcqs p, bounded-below E and Q. These hypotheses were checked in Step 1. The two projection definitions really are the counit-tensor adjuncts on their respective sites. Hence the conclusion is equality of those maps, not just transfer of their invertibility.

For Step 4 I checked the statements of the canonical sheaf open comparison, both exactness nodes, the ordinary etale open derived tensor lemma and the general pro-etale open normalization. The comparison is extended termwise using exactness. The last node explicitly asserts derived full faithfulness of j! and identity of the restricted canonical tensor map for arbitrary complexes. The ordinary etale tensor node fixes its map as the derived sheaf tensor identity, so its restriction is also the identity, by the written pure-tensor check on the defining models. The canonical open comparison is the adjoint comparison of 09AF, so under the open units its restriction is the same identity. The common source is extended by zero using V(gamma_e) followed by e_D. Derived full faithfulness therefore really detects equality here. I do not use geometric stalks to detect arbitrary pro-etale maps, and I do not invoke the restricted locally free open-transport node. This step is elementary relative to the cited normalization statements: identify the source with j! of its restriction, compute both restrictions, and use full faithfulness.

For Step 5 I opened the statements of compact-support site coherence and class comparison. The former explicitly defines B as R_p(e) composed with b and asserts its invertibility on D+ with no absolute separatedness assumption. The latter is the canonical inverse comparison C of the item. Both use the same adjoint open and counit-mate proper factors, so the equation C=B inverse fixes the named morphism. The chosen-compactification projection composite is explicitly in `def-exchange-projection`; the ordinary etale composite is fixed in this item's statement. No witness-change or compactification-independence theorem is needed.

For Step 6 I checked the type of each line of the pasted equality. The first is naturality of b at gamma_e; the second substitutes exactly Steps 3 and 4; the third is naturality of the counit-defined pro-etale projection map at e_M. The B_M factor emerges as R_p(e_M)b_E, not in the opposite order. Every line starts at V_Y(F_fM tensor H) and ends at P_fV_XD. Step 7 cancels the same B_M and B_D. This produces exactly C_D PF_p = V(PF_e)t(C_M tensor 1), including the target pullback/tensor identification; composing natural transformations and their inverses gives the stated naturality. The final two steps contain no additional theorem disguised by “transport”.

I checked delivery-errors B through E against the files: no new statements, nodes or notions need auditing; every cited result is used through its statement and has its verbatim quote in citations.json; no clause is moved into a replacement node; the statement has not been weakened; the non-Cartesian site square is legitimate; and there is no assumption that schemes over k are separated. No source from SGA is used. All seven steps are below 2000 characters, and the argument contains no hidden independent sublemma: the only mathematical black boxes are the existing cited nodes, while the open square and final cancellation are written out.

I tested M=0, H=0, the empty source, j=id, and p=id. The maps reduce respectively to the unique zero maps, the proper square alone, and the open square alone. A ramified E and n>1 do not cause a coefficient-flatness assumption: the proof uses the actual finite ring A and its stated Tor hypothesis on H. No denominator or division by the coefficient order appears. I also checked the proposed citation closures against the current DAG: none reaches this item. The proof dependency list is exactly the union of the step uses. The chapter, unit and statement dependencies are preserved.

## Unfinished work

None within the one-level stage-1 task. The cited unsplit nodes remain their existing separate tasks; no Lean proof claim is made here. Delivery is subject to the required server dry run and independent maintainer review.
