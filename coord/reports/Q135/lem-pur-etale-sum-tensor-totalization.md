# Q135: lem-pur-etale-sum-tensor-totalization

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-etale-sum-tensor-totalization.json`: item split into seven steps; not a Mathlib leaf. No new nodes and no Mathlib leaves created.
- `citations.json`: verbatim statement excerpts for every step/node citation.
- `report.md`: this report. `write_split.py` is sandbox-only preparation, not a delivery file.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` source for the exact blueprint tag and the sum-extension/lower-shriek terminology, then its etale six-functor subtree for total tensor and homotopy comparisons. Found the etale lower-shriek adjunction and additive/left-adjoint instances, finite-etale comparisons and tensor constructions; none states this entire comparison of arbitrary unbounded complexes with its generator and homotopy normalization. Upstream master is not treated as proof evidence.

## WANTED

None.

## What needed repair

The item arrived as a statement-only extraction from Q144's support-map compatibility proof, with no proof and no lean audit attachment. It is still unsplit in the shared repository. The interrupted Q135 turn left only `searches.jsonl` and brief markers; no node, report, or delivery process survived. I retained and inspected those search results and reused them. The existing item's Q144 searches are preserved, and Q135 searches are appended exactly as logged. I additionally read the candidate Mathlib totalization and homotopy constructions at `Algebra/Homology/TotalComplex.lean:438`, `Bifunctor.lean:274`, and `BifunctorHomotopy.lean:178,190`: they provide general machinery, not the specific etale sheaf comparison and sum comparison required here.

There is no mathematical statement dispute. I retained all hypotheses and conclusions and clarified that the homotopy categories mean chain maps modulo the displayed homotopies. The previous statement dependency on the derived category was unnecessary; the existing `def-pur-kinjective-complex` states the chain-homotopy equation actually used and replaces it. This uses only that definition's first sentence and imposes no K-injectivity hypothesis.

No unit or chapter record is changed. The current shared node belongs to `sk-thm-sf-compatibility`; its ancestry still points to `lem-pur-co-smooth-etale-locality`, through `lem-pur-etale-support-map-compatibility`. I read both the chapter and unit records and retained that binding. The proof supplies the unbounded-complex normalization needed for the unit's projection compatibilities. The existing blueprint search finds no imported node stating this whole lemma. Searches for `sum tensor`, `total tensor`, `sum extension`, and `0GKF` found definitions, general derived-tensor facts and the etale adjoint locality result, not an alternative copy of this item.

## Not duplicates

No new nodes are proposed. In particular I reuse `lem-pur-etale-sheaf-projection-map` for the sheaf isomorphism and its generator normalization, `lem-weil-pbc-etale-restriction-injectives` for the actual sum adjunction, and the existing Mathlib leaf `lem-weil-pbc-left-adjoint-preserves-colimits`. I did not create nodes for the coproduct specialization, naturality squares, sign cancellations, or passage to a quotient category. The ringed-slice tensor isomorphism only supplies an abstract sheaf isomorphism and does not itself assert the generator normalization, so it is not used in place of the more precise existing projection-map node.

## Review by Q135

I read Stacks `more-etale.tex`, Tag 0GKF (`lemma-f-shriek-projection`), including the pure-tensor construction and stalk comparison. This is the sheaf-level source, not a source asserting the entire unbounded-complex lemma verbatim. I also read `categories.tex`, Tag 0038 (`lemma-adjoint-exact`), `homology.tex`, Section 010V's displayed cochain-homotopy equation and Tag 012Z (`definition-associated-simple-complex`), and the existing blueprint sum-adjunction proof. The totalization and homotopy assembly are marked agent-written. I used no SGA source. There are no new nodes requiring additional sources.

For Step 1 I opened the statement of `lem-weil-pbc-etale-restriction-injectives`: it explicitly asserts that the very lift-indexed sum extension is left adjoint to inverse image for an etale map and constant coefficients. I use that clause, without taking an unstated formula from its proof. The statement of `lem-weil-pbc-left-adjoint-preserves-colimits` explicitly carries colimits to colimits and identifies the canonical comparison as an isomorphism. Its indexing category here is the small discrete category of the chosen small family, so its smallness hypothesis holds. `def-pc-tensor-complex-sheaves` explicitly says the module-sheaf category has all direct sums. The coprojection equation determines the comparison and proves its naturality directly. The exact sum adjunction is a generic off-unit tool; its purpose is declared in `split_report.tool_uses`. The colimit lemma is already a Mathlib leaf.

For Step 2 I checked `def-weil-pbc-etale-sum-extension` gives precisely the presheaf generators used to show that extension preserves sums and negatives of maps. Equality is checked on the induced generators, then on their sheafifications. `prop-weil-pbc-inverse-image-modules-exact` explicitly asserts additivity for constant-ring module inverse image. `def-pc-cochain-complex-modules` gives the differential-square and chain-map equations which the additive functors preserve. This step does not use flatness or tensor exactness.

For Step 3 I read `lem-pur-etale-sheaf-projection-map` in full. It explicitly supplies a natural isomorphism with exactly the direction, tensor-factor order and lift-generator formula of this item. Its hypotheses are satisfied by the item's commutative ring and separated etale finite-type map. Applying it to each pair of degrees uses no boundedness assumption. The degreewise direct sum of those isomorphisms followed by the comparison from Step 1 has the displayed inverse. The quoted total-tensor definition gives precisely those degree terms, including infinite diagonal sums. This is an application of an existing smaller sheaf lemma, not a new lemma restating the whole item.

For Step 4 the same projection-map statement supplies naturality for arbitrary sheaf maps, hence for each of the two differentials. I wrote the two equations, not an assertion that an unspecified identification respects differentials. The total-complex definition supplies the coefficient on the second differential, which is the same on both sides. Step 2 supplies additivity when applying extension to that signed sum. Testing on each coprojection proves equality as sheaf maps, and multiplying by the inverse proves that the inverse is a chain map. No conservativity test on derived morphisms is used.

For Step 5 the projection statement's naturality in both sheaf variables is exactly what is used for the two degreewise components of chain maps. The total-tensor definition supplies their summand action. The naturality of the sum comparison was already proved in Step 1, so this step uses neither an unrecorded totalization-comparison theorem nor the proof of a cited node.

For Steps 6 and 7 I checked the first sentence of `def-pur-kinjective-complex` against the actual equation used; it is the general cochain-homotopy equation and has no K-injectivity assumption. The cited total-tensor definition supplies the full signed differential. In the first-variable calculation the mixed terms cancel because their coefficients are $(-1)^{p-1}$ and $(-1)^p$; in the second-variable calculation the chosen homotopy has the necessary extra $(-1)^p$, making the first-differential terms cancel and the second-differential terms have coefficient one. The existing sheaf projection is natural for degree-$-1$ component maps as ordinary sheaf maps, so it intertwines the resulting homotopies themselves. This proves compatibility, rather than merely checking source and target objects. Passing the naturality equation to homotopy classes is then the definition of the quotient functors. Each calculation is elementary once these cited formulas are available; it introduces no hidden general comparison lemma.

I checked delivery-errors B1–B10: there are no new statement-only nodes, no invented terminology, no duplicated theorem, and no new Mathlib leaf claim. Item sources use the actual Stacks tags and labels. All recorded searches are actual log entries and all services were available for them. I checked C1–C8 by opening every cited node's statement and writing verbatim citation excerpts; there is no proof-only citation, missing hypothesis or cycle introduced by the chosen dependencies. The off-unit adjunction is declared as a tool instead of silently replacing a route. I checked D1–D5: the construction remains in this item's proof, using pre-existing smaller facts; it is not moved into a new node. I checked E1–E7 against the objects, signs and hypotheses at each use.

Small cases checked directly: identity $u$ gives the usual identity on every summand; an empty source or zero coefficient ring gives the zero complexes; an empty indexing set in Step 1 is the initial object; a single nonzero bidegree gives the sheaf comparison; degrees of either parity (including negative odd degrees) satisfy the two cancellation identities. Infinite diagonals pose no convergence or finite-sum requirement: each source summand maps to one target summand, and its differential to two. None of the steps assumes flat terms, K-flat representatives, constructibility, Noetherian schemes or boundedness. The largest step is 1309 characters, so there is no step above the human's 2000-character review threshold.

## Unfinished work

None in this one-level split. The existing cited lemmas keep their own states and proof obligations; this delivery does not claim their Lean proofs are complete. No Lean was written and no compiler, Lake or build tool was run. Server dry-run validation is the remaining delivery gate.

## Validation

The required server dry run exited successfully: `OK (not pushed) deliver/Q135/lem-pur-etale-sum-tensor-totalization at 8fb7f48bfd: preflight passed`. The node and citation files passed unchanged. Proceeded to the authorized direct delivery after that process exited.
