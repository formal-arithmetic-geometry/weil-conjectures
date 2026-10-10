# Stage 1 delivery: `lem-weil-pbc-closed-pushforward-constant-stalks`

## Worker report

Split the parent into the locally constant sheaf assertion, the stalk evaluation
on the closed subset, and the singleton stalk off it. Created the unsplit nodes
`lem-weil-pbc-locally-constant-maps-sheaf` and
`lem-weil-pbc-locally-constant-germ-evaluation`. No Lean was written. The new
nodes record LeanSearch, LeanFinder, and Mathlib source searches. No attachment
or WANTED source is reported.

## Review by C1

I read `literature/stacks-project/sheaves.tex` at the paragraph preceding
Definition 006W, Example 007B, and Lemma 00AE and its proof. The parent states
exactly the set-valued constant sheaf on a closed subspace and its stalks; it
does not claim the additional abelian-sheaf or inverse-image assertions of 00AE.
The sheaf child uses the same local-constancy definition and open-cover
hypotheses as 006W. The germ child gives the neighbourhood colimit and the
evaluation map of 007B explicitly. Both children are self-contained and have
empty proof and proof-dependency fields while unsplit. I searched the current
DAG by the local-constancy and stalk terms and found no node stating either
child's fact; their recorded searches show no exact Mathlib match.

Step 1 uses the sheaf child's pointwise gluing statement on the subspace C;
the cover of an open V in T restricts to an open cover of V intersect C. Step 2
uses the category-colimit definition and the germ child's evaluation theorem;
every neighbourhood of x in C comes from one in T, so the two germ relations
coincide. Step 3 uses the same colimit definition and the open neighbourhood
T minus C, where the empty domain has one map. No step assumes separation or
nonemptiness of R. In the edge cases C empty and R empty, the off-C singleton
claim and the on-C universal claim respectively still hold. The worker's
refinement made the neighbourhood comparison and definition dependencies
explicit; I requested no further correction.

`review_split.py` passes. `check_dag.py` reports no cycles and seven existing
reachability warnings on unrelated nodes; none is introduced by this item.
