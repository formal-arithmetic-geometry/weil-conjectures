# Stage-1 report: lem-pc-ring-pseudo-coherent-distinguished-triangle

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-ring-pseudo-coherent-distinguished-triangle.json`: split Tag 064R into the finite-free cone proof and rotation argument; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-ring-derived-map-lift.json`: statement-only Tag 064E auxiliary; no Mathlib match.
- `citations.json`: verbatim statement quotes for every cited step dependency.

## Attachments

None. A source grep found no sorry-free declaration carrying the target tag or exact ring-level statement.

## WANTED

None.

## Not duplicates

lem-pc-ring-pseudo-coherent-distinguished-triangle vs lem-pc-pseudo-coherent-distinguished-triangle: the new node is the ring-level three-clause $m$-pseudo-coherence result in $D(R)$, while the existing node is a scheme-level implication for ordinary pseudo-coherence in $D(\mathcal O_Y)$.

lem-pc-ring-pseudo-coherent-distinguished-triangle vs lem-pc-pseudo-coherent-distinguished-triangle: the former is the ring-level three-clause $m$-statement, while the latter is a scheme-level ordinary pseudo-coherence implication.
lem-weil-pbc-five-lemma vs lem-pc-ring-pseudo-coherent-distinguished-triangle: the existing node is the generic finite five-lemma for exact sequences, while the item is the ring-specific pseudo-coherence theorem; the former is used as a generic tool for the long exact cohomology segments.

## What was checked

I read More Algebra, Tag 064R (`more-algebra-lemma-cone-pseudo-coherent`) and the referenced Derived Categories lifting lemma Tag 064E in `/home/ubuntu/c1-stacks-review/more-algebra.tex`. The target statement matches 064R hypothesis by hypothesis: arbitrary ring, integer, derived category of modules, and all three clauses. Step 1 uses the finite-free witnesses and truncation from 064R, the exact chain-map lifting assertion of `lem-pc-ring-derived-map-lift`, the cone and localization structure stated by `def-weil-abstract-derived-category`, and the five-lemma conclusion from `lem-weil-pbc-five-lemma`; these statements say the facts used. Step 2 uses the triangulated shift structure in `def-weil-abstract-derived-category` and spells out the cyclic relabelling and shift for the third clause.

I searched the DAG and blueprint for the three-clause ring statement and found only the cyclic first-clause node `lem-sc-cone-pseudo-coherent`; I retained the independent Tag 064E lift node and reused the existing generic five-lemma tool. I tested the target on the zero triangle and on a split triangle of one-term finite-free complexes; all degree bounds reduce as stated.

## Review by E1

I checked the source and auxiliary statements hypothesis by hypothesis. The map-lift node states exactly the representation used in Step 1, the abstract-derived-category node states localization, cones, triangles and shifts, and the existing five-lemma node states the isomorphism conclusion used on each exact cohomology segment. Step 2 explicitly accounts for rotation and the shifted third object. The item’s `proof_deps` is the union of the step uses, and every `citations.json` quote is a verbatim substring of the cited statement. The five-lemma citation is declared as a generic tool; the item route remains Tag 064R. Edge-case checks were performed separately on the zero and split one-term triangles.

## What was wrong and what changed

The imported item was unsplit and had no proof. I supplied the Tag 064R mapping-cone route, corrected the auxiliary node's erroneous `def-pc-derived-category` label to `def-weil-abstract-derived-category`, and avoided the cyclic existing first-clause node by introducing only the strictly smaller 064E lift statement.

## Unfinished

Nothing.

## Second reading by E1

- Item statement: reread More Algebra Tag 064R (`lemma-cone-pseudo-coherent`) at the source lines; verdict: the ring, integer, derived-category, witness, and all three hypotheses/conclusions agree hypothesis by hypothesis.
- Step 1: checked against the full Tag 064R proof, `lem-pc-ring-derived-map-lift`, `def-weil-abstract-derived-category`, `lem-weil-pbc-five-lemma`, and `lem-sc-four-lemma`; verdict: the cone witness, higher-degree five-lemma isomorphisms, and degree-$m$ four-lemma surjection are all stated with their needed hypotheses.
- Step 2: checked against Tag 064R assertions (2) and (3) and the shift clause of `def-weil-abstract-derived-category`; verdict: both rotations and the index change $H^i(X[1])=H^{i+1}(X)$ are written explicitly, including the $(m-1)$ application for the second clause.
- New node `lem-pc-ring-derived-map-lift`: checked against Tag 064E (`derived-lemma-lift-map`) and searched the DAG for duplicates; verdict: self-contained statement-only auxiliary, no existing node or Mathlib declaration gives the exact bounded-projective lifting fact.
- Existing dependencies: read the statements of `def-weil-abstract-derived-category`, `lem-weil-pbc-five-lemma`, and `lem-sc-four-lemma`; verdict: each citation supplies exactly the fact used, with no proof-only dependency.
- Edge cases: tested the zero triangle, a split triangle of one-term finite-free complexes, $m=0$, and $m=1$; verdict: the witness bounds and shift indices reduce correctly.

Changes made: added the missing four-lemma citation and degree-$m$ argument; expanded both rotation arguments with the correct shift index; added the corresponding verbatim citation quote; retained the single strictly smaller Tag 064E auxiliary node.
