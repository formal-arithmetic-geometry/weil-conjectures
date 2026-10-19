# Stage-1 report: def-rp-weight-blocks

## Files written

- `dag/nodes/sec-purity-real-sheaves/def-rp-weight-blocks.json` — repaired definition split; no new nodes, no Mathlib leaves.
- `citations.json` — empty list: this definition has no numbered proof steps.
- `current-citation-statements.json` — read-only citation snapshot for this repair, not a delivered DAG node.

## Attachments

None. The read-only slopmaster2 source has no exact declaration for every clause. `AlgebraicGeometry.WeilGroup.HasDetWeight` in `WeilConjectures/EtaleCohomology/Purity/RealSheaves/Weights.lean:121` defines the predicate for an individual weight. `Representation.weightMultiset` in `WeilConjectures/AlgebraicGeometry/LinearAlgebraicGroup/Weights.lean:172` repeats weights by rank for a chosen family of subrepresentations, but neither declaration supplies the constituent multiset, the intrinsic semisimple blocks, and both tail sums. These are partial implementations, not an ATTACH for the complete item. Searches by the exact item tag and the notions were repeated read-only; no compiler was run.

## WANTED

None.

## What was wrong and what changed

The sole return is `coord/returns/Q132.md`, entry for returned branch head `c0b0d5d752`: landing detected that `def-real-weil-representation-operations` had changed since review. The retained item was compared with the current shared DAG item: the mathematical statement and all five statement dependencies agreed before this repair; the retained split additionally held its searches and split report. The current operations statement adds references to the existing ordinary representation operations and to the theorem justifying its fundamental-representation example. Its direct-sum action and identification of irreducibility with simplicity remain available verbatim.

The repair now states explicitly that the direct-sum action is componentwise and that irreducibility means nonzero with no nonzero proper stable subspace. Rank is explicitly the dimension of the underlying vector space, rather than being incorrectly credited to the operations node in the report. The explanatory paragraph expands the nonzero-projection argument by its stable kernel and image, instead of leaving it as an invocation of Schur's lemma. These are explanations of the same definitions and proof, with no change of hypotheses, conclusion, normalization, or multiplicity. The definition remains split with its five existing statement dependencies, and the delivery command rebases its owned fields onto the latest server DAG.

The earlier report incorrectly said that the current blueprint has no proof file. I opened `literature/blueprint/main-20261015/blueprint/sec-purity-real-sheaves/sk-d-real-detweights/def-rp-weight-blocks.proof.md`: it contains the choice-independence argument. That argument was already retained inside the imported statement, and remains there. I also supplied the missing `citations.json` found by the required initial dry run. The earlier Mathlib search entries are retained unchanged: this repair changes neither the search question nor the objects. No search is invented or represented as newly run.

## What could not be finished

No mathematical issue remains. The final dry run and delivery are run after these edits; their actual tool results determine the delivery status.

## Not duplicates

No new node is created. `def-mg-determinantal-weight-multiset` counts one entry per simple-factor occurrence; this item additionally repeats by rank and defines blocks and tail sums. The whole-DAG/blueprint search for weight blocks finds this item and the broader unit `sk-d-real-detweights`; the unit also includes the separate determinant-weight definition, so it is not an exact duplicate of this individual node. Generic degree-datum nodes `sk-d-weights` and `d-weights` overlap the rank-counting convention but do not define the full Weil-sheaf item. No unit realization fields need alteration: this item realizes only the block/list portion of the unit, whose individual determinant weights are a separate node.

## Review by Q132

I read the current main-20261015 item (order 2981), its complete proof file, the corresponding master definition, the current unit text and the chapter record. The normal geometrically connected curve, the fixed field isomorphism, nonzero lisse Weil sheaf, and simple factors are unchanged. The current unit uses the operations, punctual weights and rank-one purity route; the item uses the existing determinant-weight definition for that route rather than importing a new purity theorem. No SGA source is cited.

I opened all five current cited statements, not just their proof or status. `def-mg-weil-composition-series` says each factor is nonzero and has no nonzero proper stable subspace; finite dimensionality makes each rank a positive integer. `def-wf-determinantal-weight` defines the rank as dimension, chooses the unique determinant-line weight for an irreducible sheaf on precisely a normal geometrically connected curve, and divides it by that positive rank. Thus its hypotheses hold for every factor here. `def-mg-determinantal-weight-multiset` explicitly supplies one entry per occurrence of a simple summand, and states independence of the chosen series; it is used only for clause 1. `lem-mg-jordan-holder` states that any two finite-dimensional Weil composition series have the same factors up to permutation and isomorphism with the same multiplicities. It is used for the choice of factors; it is not credited with any tensor, rank, or block theorem.

For the changed citation, I read `def-real-weil-representation-operations` in the current DAG and main-20261015 source (order 2930). Its direct-sum clause says that the action on a pair is componentwise; its irreducibility clause identifies irreducible with simple in the composition-series sense. Those are precisely the meanings now written explicitly in clause 3. The added generic-operation references and justification for the fundamental-representation example do not alter either meaning. We do not take rank additivity or Schur's lemma from this definition. In the preserved explanation, finite partial sums have successive quotients the indicated simple summands, so Jordan–Holder applies; dimensions telescope along a composition series, giving list length equal to the rank. An isomorphism conjugates each action, preserves its dimension and determinant, and hence preserves the unique determinant-line weight. Thus regrouping factors preserves both numerical multisets and the finite tail sums.

For the intrinsic block, every chosen summand of weight gamma is included among the simple subobjects of that weight. Conversely, the projection from any simple subobject W to a summand is equivariant by the componentwise action. Its stable kernel is either zero or W and its stable image is either zero or the summand. A nonzero projection is therefore an isomorphism. Projections to different-weight summands vanish, so W is contained in the direct sum of same-weight summands. This identifies the block as a subobject independently of the decomposition, even for repeated isomorphic constituents. These are the actual definitions and elementary vector-space arguments used; none is an uncited non-elementary theorem hidden behind the changed operations reference. Since the item is a definition, its proof/proof_deps arrays remain empty, as in the approved delivery, and citations.json is empty. There are no numbered proof steps or long proof-step objects to audit.

I tested a single rank-one factor, a rank-three irreducible (three rank-counted entries but one constituent entry), repeated isomorphic summands, two nonisomorphic simple summands of equal weight, and distinct weights. A threshold equal to a constituent weight excludes that block from both strictly-above sums. A threshold above all weights gives zero tail rank and sum; below all weights it gives total rank and total rank-weighted sum. The zero block for a missing weight is the empty direct sum; if the semisimple object is zero the same empty-sum convention applies. The rank-one/rank-three examples test counting rather than asserting any extra existence theorem. No new statement needs a separate small-case check or Mathlib search. The B--E review finds no new nodes, renamed clauses, new route, changed coefficient category, added hypothesis or cycle.

The following hashes pin the exact current statements reread for this repair; all were checked against the saved citation snapshot before delivery:

- `def-mg-weil-composition-series`: statement SHA-256 `0aaf4ef27052c931ddc60ac3a7d417aea3ee97515af14a5dfc29e9aa10319c86`.
- `def-wf-determinantal-weight`: statement SHA-256 `d0ff2c352534786defe0ed8316135e094e44521550016cf97c5de60a76ebd94b`.
- `def-mg-determinantal-weight-multiset`: statement SHA-256 `f6060d775d616ea811c246b86a46c085e0f551cfa3081d9750c2801245135b96`.
- `def-real-weil-representation-operations`: statement SHA-256 `b85310bf4fe7c0c12ad7bb0f14d5e15ae2bef523f0910f99d33390f717185cdd`.
- `lem-mg-jordan-holder`: statement SHA-256 `56878e4c396dfd9033b3a8aee53c0a28fb0b92ab78cf07b2f89d3c7e0eac6cca`.
