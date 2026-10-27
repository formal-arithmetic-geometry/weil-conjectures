# Worker report: lem-sfb-profinite-field-scalar-annihilator-hull

Disposition: ABANDON, inability to prove the generation assertion, not a statement dispute or a tool failure. No completed split or delivery is claimed.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-profinite-field-scalar-annihilator-hull.json`: copy of the live unsplit item, retaining its entire statement, source, blueprint information and earlier searches; appended the actual searches from this attempt. Status remains unsplit; no proof steps were invented.
- `searches.jsonl`: five actual searches, whose returned hits were read. The first and second LeanFinder phrasings, LeanSearch, Loogle and Mathlib grep found no match.
- `citations.json`: empty, since there are no proof steps.
- `hrs.txt`, `rtw.txt`: local text extractions from the two available papers, for reading in this sandbox.
- `report.md`: this report.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searched the live project source under `lean/WeilConjectures` for the item id, profinite annihilators and continuous/Stonean scalar-kernel notions. No declaration states this assertion.

## WANTED

WANTED: A proof or precise reference for ordinary, uncompleted derived generation of the actual sheaf kernel of a continuous E-valued scalar on Prof/P from finite locally free R_E-modules using precisely products, shifts, triangles, retracts and the specified bounded strict filtered colimits. HRS Example 4.2 and Remark 6.4 explain the obstruction but do not assert this generation result. No new source was downloaded.

## What was wrong or could not be finished

The live item itself explicitly says that the exact generation reference is WANTED. I did not establish that the statement is false, so it is not marked STATEMENT-DISPUTED and no hypothesis or conclusion has been changed. Its assertion is substantially stronger than the elementary scalar-annihilator calculation in HRS Theorem 6.12(2).

The complete obstruction to the easiest candidate proof is as follows. Let P=beta(N_{>=1}), E=Q_ell and a(n)=ell^n, extended continuously to P. Let U_k be the clopen closure of {n>=k}, e_k its characteristic function, and M_k=e_k R_E with transition M_{k+1}->M_k the inclusion. Every M_k[0] is a retract of R_E[0], so belongs to any class J in the item. On EVERY profinite test b:Q->P, the ordinary inverse limit of these inclusions consists of continuous x vanishing on b^{-1}(N), which is exactly K_a(Q). Thus the ordinary sheaf limit is K_a; no scalar-extension identification has been used.

However, its Roos endomorphism on the product is not an epimorphism. In product sections over P put y_k=ell^{-k}1_{ {k} }. Each y_k is a continuous section of M_k: the singleton {k} is clopen, and each fixed section has only two values. If x_k-x_{k+1}=y_k, evaluate at n>=k. Since x_{n+1}(n)=0, backward recursion forces x_k(n)=ell^{-n}. For any fixed k this is unbounded on n>=k. A continuous function from compact P into Q_ell has bounded image, so such x_k cannot exist. Evaluation at this extremally disconnected P is exact (finite covers split by Stonean projectivity, as in the already reviewed relative finite-bundle Roos lemma). Hence failure of surjectivity on P proves failure of sheaf epimorphy. The product fibre therefore has nonzero degree-one cohomology and cannot simply be identified with K_a[0]. This rules out using ordinary derived products to obtain this inverse limit in a single triangle.

The existing `lem-sfb-relative-finite-bundle-roos` does not fix this: its Roos exactness hypothesis is that each term is a finite locally constant group bundle. M_k has an E-valued fibre. The same node separately gives exact products on Prof/P, but exact products alone do not make this 1-s surjective. I opened and read its complete statement and proof, including its compact solution-cover argument; that argument uses finite compact fibres.

The integral scalar realization node and its finite reductions were also examined. They supply O_E-module finite-bundle towers. The finite quotients O_E/pi^r cannot be nonzero E-module sheaves, because pi is invertible in E. Thus they are not objects of the category in which this item's J lives. One cannot apply J-closure to that integral tower. Rationalizing a product is also not automatically a product of rationalizations: already (prod_k O_E)[1/pi] -> prod_k E misses the tuple (pi^{-k})_k. I found no valid bounded-colimit/product interchange which resolves this issue.

Nor can the scalar annihilator be substituted. HRS Example 4.2 and Remark 6.4 give exactly the same beta(N) example with Gamma(P,K_a)=0 but K_a nonzero on the boundary test. HRS Theorem 6.12(2) describes the annihilator ideal of C(P,E) using a clopen idempotent; it does not identify this sheaf kernel with scalar extension of that ideal.

I also checked the available solid-rigidity source, RTW Lemma 1.2.7 and Theorem 1.2.8. Its statements concern integral solid sheaves, their finite torsion inverse limits, and an Ind(Pro(...)) presentation. I found no statement there directly providing this E-linear relative ordinary-derived-hull assertion with these generators. No switch to a solidified category is made.

Without a construction removing the extra cohomology or an independent smaller theorem that genuinely supplies it, creating a node saying the desired annihilator belongs to the hull would simply rename the item (D1/D2). I have not done that. The remaining unproved obligation is the entire nontrivial generation step, rather than a routine citation or a source typo.

## Blueprint and duplicate searches

Read GOAL.md, the three blueprint levels in SETUP.md, stages/1-dag.md, the worker brief, and delivery-errors B--E. Opened the chapter/unit records, the latest blueprint's compactification-coherence unit and `det-sf-comp-coherence-cocycle.proof.md`, and `det-sf-comp-coherence-refinement.proof.md`. This is an auxiliary descendant of the refinement-isomorphism paragraph via the supported-image and relation-hull nodes; no chapter or unit route was modified.

Ran `tools/blueprint_refs.py ancestor lem-sfb-profinite-field-scalar-annihilator-hull` and searches for `annihilator`, `annihilator field`, `profinite kernel` and `truncation`. Searched the whole DAG for continuous scalar annihilators, finite-model kernel hulls, profinite generation, clopen towers and relevant product/truncation results. Read the parent relation-hull statement and proof. Its field step explicitly depends on this item, so citing it back would be circular. Read the integral-realization and relative finite-bundle Roos nodes. No existing theorem found supplies the missing generation. No new ids were created, hence no duplicate pairs require adjudication.

## Review by NA

I read HRS Example 3.1 (continuous coefficients), Lemma 4.1, Example 4.2, Remark 6.4, and Theorem 6.12(2), especially its principal-annihilator argument. The item's actual sheaf kernel agrees with the phenomenon described in Example 4.2/Remark 6.4. Those sources do not prove membership in the newly specified hull, and I have not attributed that conclusion to them. I read RTW Lemma 1.2.7 and Theorem 1.2.8 as a possible integral/solid approach and rejected their use as an unstated E-linear generation theorem.

There are no submitted proof steps or cited-node quotes to certify. For the attempted proof I checked each potential cited statement against the hypotheses in force: relative finite-bundle Roos requires finite bundle fibres; integral realization uses the coefficient O_E, not E; the parent relation-hull theorem depends on this item. Thus none can be used to close the missing step. The explicit unbounded tuple above corrects the initially plausible but false Roos-surjectivity argument. It is a counterexample to that proposed proof step, not a counterexample to the item.

Checked the stated easy cases: empty P gives zero; a=0 gives R_E; an invertible a gives zero; for a clopen zero locus, K_a is a clopen idempotent summand of R_E and belongs by retract closure. The unresolved case is a non-clopen zero locus, already exhibited by beta(N). No non-elementary long proof step has been hidden, and no elementary calculation was inflated into a node. No Lean file, compiler, Lake command, git command in the read clone, repository file or launcher file was touched.

## Validation and delivery

No dry run or push was launched: the mathematical split is incomplete, so marking it split and pushing would be false. No tool failure is claimed. The sandbox preserves the actual search log and this precise failure analysis for a future attempt.
