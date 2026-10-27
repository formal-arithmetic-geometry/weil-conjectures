# Stage-1 delivery: lem-trf-free-normalized-homology-surjectivity-transfer

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-free-normalized-homology-surjectivity-transfer.json`: existing statement split into four explicit elementary calculations; statement unchanged. Mathlib verdict: no exact match or one-line specialization found.
- `citations.json`: verbatim statement quotations for every cited node in each step.
- `search-1.txt` through `search-5.txt`, `searches.jsonl`: actual current-session search results, retained for inspection. The item's earlier NF search records are preserved as inherited records, not represented as Q03 searches.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the whole project `lean/WeilConjectures/` by the exact blueprint tag and by normalized/Moore, surjectivity, evaluation, free abelian and simplicial terminology. No declaration giving all clauses of this item was found. Unrelated normalized evaluation statements concern torsors or tensor comparison, not this simplicial evaluation square.

## WANTED

None. The source is present locally.

## Issues found and changes

The imported item was an unsplit, self-contained fragment of Stacks Tag 08P2 (`lemma-homotopy-equivalence`). Its statement is correct as written. The source uses the normalization with the last face as differential; the item instead defines the intersection of kernels of faces 1 through n with differential d_0. No comparison theorem between the two normalizations is used: the source's lifting argument works directly because every face of a positive-degree normalized cycle vanishes. Degree zero needs separate treatment and is explicitly included.

The current blueprint was read at `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.{md,proof.md}` and its unit/chapter records were read. The distant existing provenance is retained; this split only supplies the previously introduced simplicial input and changes no unit or chapter route. No repair note exists for the item.

Mathlib searches were run through the prescribed msearch.py command: LeanFinder with two distinct formulations, Loogle, grep under AlgebraicTopology, and LeanSearch. All services answered successfully. The complete hits were read. Group homology epimorphism results require group/representation data and do not assert the desired evaluation transfer. The normalized Moore complex hits provide the complex and induced map, not the full item. Inspected `Mathlib/AlgebraicTopology/MooreComplex.lean` lines 64–136 and `Mathlib/GroupTheory/FreeAbelianGroup.lean` lines 124–126. The latter's generator evaluation identity does not by itself state the normalized cycle lifting and homology conclusion. The proof therefore remains a split, not a Mathlib leaf.

## Unfinished work

None in this stage-1 item. No Lean was written or compiled.

## Not duplicates

No new nodes. Searches of the DAG for Tag 08P2 and normalized-cycle terminology found the parent quasi-isomorphism node and the separate injectivity/free-homotopy siblings. These do not supply an independent result needed in this elementary surjectivity proof. Whole-blueprint searches with `blueprint_refs.py search` for `normalized homology`, `08P2`, and `free abelian` found no equivalent blueprint statement; `same_as` stays empty.

## Review by Q03

I read the evaluation square and complete surjectivity paragraph of Stacks `simplicial.tex`, Tag 08P2, lines 5895–5932, with the adjoining statement and injectivity paragraph. There are no new nodes needing separate sources. I opened both cited definition nodes and read their statements rather than relying on their titles. The simplicial-object node defines a contravariant functor and its face/degeneracy operators, and defines morphisms as natural transformations. The simplicial-set node likewise defines simplicial sets and natural transformations. Those are precisely the notions used; neither definition is cited as a theorem about homology.

Step 1 uses both definitions to check operators, naturality of F(a), naturality of evaluation, and the square on generators and then finite sums. The only algebra is additivity of operators in the category of abelian groups. Step 2 uses the functor/face/morphism definitions from the simplicial-object node. The displayed face identities follow by equality of the corresponding order-preserving injections; they show explicitly that d_0 preserves normalization and squares to zero. Commutation with an additive simplicial map proves preservation of kernels and images directly, hence descent to the quotient; no exactness, Dold–Kan, or homology comparison theorem is hidden here. Step 3 uses the same face definition and additivity: each face of [y]-[0] is literally [0]-[0]. Step 4 cites no additional node, because it only applies the earlier established square and cycle lift and writes out equality modulo the explicitly defined boundary subgroup. The boundary v comes from the assumption of surjectivity on free normalized homology, not from any unassumed surjectivity of f on simplices. Its evaluation is normalized by step 2, so the final boundary really lies in the correct quotient.

I checked all hypotheses: arbitrary simplicial abelian groups, an additive simplicial f, and only a fixed n with surjectivity upstairs. No homotopy equivalence, degreewise epimorphism, boundedness, finiteness or injectivity is assumed. For n=0 the cycle condition is automatic and the final boundary is still d_0 of a normalized element in degree 1. For n=1 the two faces of the lifted cycle are both zero. For the zero simplicial group and for y=0 the lift is [0]-[0]=0, even though the basis vector [0] itself is not zero. The argument does not incorrectly treat y -> [y]-[0] as an additive section.

Against delivery-errors B: all notions are already inline or cited; TeX escaping and the exact tag/label were checked; no new-node or Mathlib-leaf claims are made and searches are actual logged calls. Against C: every citation's statement was read, all quotations in citations.json were checked as verbatim substrings, and no non-elementary uncited result is used. Against D: the proof carries the argument and introduces no restatement node; no appeal to a definition substitutes for a theorem. Against E: the degree-zero convention, zero generator, boundary sign, normalized membership, and evaluation compatibility were checked as above. All four steps are below 2000 characters (606, 635, 521, 714); no long step conceals an independent lemma. The correction from the source is only the explicit choice of face convention already present in the unchanged imported statement.
