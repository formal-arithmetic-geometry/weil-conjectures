# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-projection-section-normalization.json`: existing statement, now split with one proof step; no new nodes and no Mathlib leaves.
- `citations.json`: one verbatim statement quotation for the cited projection-coherence node.
- `searches.jsonl`: the five prescribed Mathlib searches and their returned hits.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact item id, projection-section terminology, and projection-formula names; no sorry-free project declaration states this item. The existing project declarations found by broader keyword searches do not state the item.

## WANTED

None. The proof uses the existing DAG statement `lem-sfb-ringed-projection-tensor-composition`; its source is already recorded in that node and no additional archival source is needed for this split.

## Corrections and source observations

The imported node had an empty proof despite its statement being the section specialization of the existing general ringed-topos projection-coherence lemma. I did not change the statement or its hypotheses. The proof now explicitly instantiates the general lemma with (i:X\to V), (r:V\to X), and coefficient object (R_X), checks the pro-etale ringed-topos hypotheses, and identifies the two arrows with the item’s π map and (Rr_*(a_M)). Properness is part of the item’s setup but is not needed by the generic coherence identity. No duplicate or clause-restating node was created.

## Review by Q94

I read the item node, the chapter `sec-six-functors-basics`, unit `sk-thm-int-restriction`, and the source proof `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-int-restriction/sk-thm-int-restriction-line.proof.md`, including the clause that uses diagonal projection cancellation. I also opened the complete statement of `lem-sfb-ringed-projection-tensor-composition` and verified that its final “In particular” clause gives the identity for a morphism (p) with a section (i), with tensor symmetry and canonical direct-image/pullback comparisons explicitly included.

The sole item step uses the final clause of lem-sfb-ringed-projection-tensor-composition and the setup statements of sk-def-sfb-module-derived-pushpull, def-sfb-module-derived-pushpull-adjunction, sk-def-sfb-derived-tensor-hom, and sk-def-sfb-dc-setting. I checked their hypotheses one by one: the pro-etale module categories and derived adjunctions are the ringed-topos data supplied by `sk-def-sfb-module-derived-pushpull`, `def-sfb-module-derived-pushpull-adjunction`, and `sk-def-sfb-derived-tensor-hom`; the coefficient sites and commutative pulled-back rings come from `sk-def-sfb-dc-setting`; and (ri=1_X) supplies the required composite isomorphism. Substituting (p=r), (W=V), and the cited lemma’s (V=R_X), its first projection arrow is the item’s (pi_{r,M,Ri_*R_X}) by the stated tensor-symmetry convention. Its second arrow is the (i)-projection map, which becomes (a_M) after (i^*r^*M\simeq M); the canonical (Rr_*Ri_*\simeq1) is the same comparison used in the cited statement. Thus the cited identity is exactly the displayed conclusion. The step is non-elementary because it invokes that general coherence theorem; no uncited fact is hidden in it.

I searched the whole DAG for projection-coherence, section-normalization, and the relevant Stacks/Mathlib terminology before reusing the existing node; its statement is strictly more general and already covers the required specialization. The five current Mathlib searches (LeanFinder, Loogle, grep, LeanSearch, and a second LeanFinder phrasing) returned only abstract categorical, normalization, or monoidal facts, so `mathlib_match` remains null. I tested the specialization at (r=i=1_X), where both projection maps are identities, and at (M=0), where every displayed morphism is the zero-object identity; both agree with the conclusion. The cited node is in another unit, so I recorded it in `split_report.tool_uses` as a generic route tool. The only proof step is well below 2000 characters and introduces no new node or cycle.

## What could not be finished

Nothing remains unfinished in the requested split. No Lean file, compiler, Lake, build, or live project file was written or run.
