# Stage-1 report: lem-sfb-double-fibre-null-cocycle-obstruction

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-double-fibre-null-cocycle-obstruction.json`: statement, split; no exact Mathlib match. The statement is unchanged. Five proof steps use one existing Mathlib leaf.
- `citations.json`: the verbatim statement quote for step 4's sole cited node.
- `report.md`: this report. `searches.jsonl` is the unmodified log produced by msearch.py.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the blueprint id and null-sequence, cocycle, double-fibre and closed-subgroup-exhaustion terminology in `lean/WeilConjectures/`. No declaration states the item exactly. The larger `Sheaf/Topology/NormAlgclProfiniteCechExact.lean` statement concerns algebraic-closure coefficients and an existential counterexample plus local contraction, not this general conditional assertion for an arbitrary noncomplete ultranormed additive group. Its docstring's construction is useful background, not evidence of an exact project attachment.

## Wanted sources

None. The motivating current blueprint and Stacks source are present. The analytic construction is explicitly agent-written, as the item's existing source says; the blueprint is not represented as proving it.

## Findings and changes

The following paragraphs record the original 2026-10-22 split. The dated repair review below supersedes their initial-state description.

The live item was unsplit with no proof. The sandbox initially contained only dispatcher marker files, no previous item, report, search log, or delivery session to resume. No statement dispute or correction was needed. Retained the statement, statement dependencies, source, blueprint ancestry, chapter, unit and created metadata. Appended only searches actually run by Q123; retained the pre-existing Q46 searches verbatim. The ancestor command returns `None` for this inherited chain, which is retained rather than inventing a blueprint ancestor.

Read the current blueprint direct-images proof, paragraph (3). It states preservation of constructible finite-Tor categories, including the open direct-image coefficient route, and does not assert this analytic cocycle theorem. Also read the recorded chapter, unit, and the three-level rule in SETUP.md. This split stays within the existing analytic auxiliary and does not replace a unit route.

Whole-DAG searches by `0CQN`, `lemma-baire-category`, Baire title/statement, null sequence and double fibres found the existing `lem-sfb-baire-closed-cover-interior`; its statement is exactly the required generic closed-cover consequence. Whole-blueprint searches for Baire, closed cover, cocycle, null-sequence and double fibre produced no equivalent item. The unrelated cocycle matches concern different categories and objects. Reused the existing generic Baire node rather than creating a duplicate or an obstruction lemma restating a clause of the item.

Ran LeanFinder twice with different phrasings, Loogle, LeanSearch and Mathlib grep through the prescribed msearch.py. All completed successfully, and their actual records are in searches.jsonl and appended to the item. The hits concern finite clopen approximations, group cohomology, continuous function groups, and dense subgroups; none states the double-fibre construction with the closed subgroup obstruction. Inspected the group-cohomology hit and the Baire declaration/instance source lines. In particular a theorem that coboundaries are cocycles does not say that this relation cocycle has no continuous primitive.

## Review by Q123

I read sections B through E of delivery-errors.md, including the repeated isolated-run copy, against the item and the available source. I read Stacks `topology.tex`, Tag 0CQN (`lemma-baire-category-locally-compact`), with its Baire statement and nested-compact-neighbourhood proof. This is used only through the existing closed-cover statement. I read the full statement of `lem-sfb-baire-closed-cover-interior`, not just its source or proof: for a nonempty locally compact Hausdorff subspace covered by countably many closed sets, one has nonempty interior. Its recorded Mathlib match is `nonempty_interior_of_iUnion_of_closed` at `Mathlib/Topology/Baire/Lemmas.lean:257`, using `BaireSpace.of_t2Space_locallyCompactSpace` at `Mathlib/Topology/Baire/LocallyCompactRegular.lean:23`; I opened those lines. There are no new nodes requiring another source review.

Step 1 uses only the hypothesized fibre classification. Every pair in R is diagonal or has exactly one of the specified orientations, the two points differ, and distinct v_k prohibit ambiguity between indices. Thus the function is actual data, without an existence theorem choosing it or a hidden arbitrary value.

Step 2 has no cited non-elementary input. At each off-diagonal point its open singleton gives a constant neighbourhood. At a diagonal point and each positive epsilon, convergence selects one N for the entire tail. The complement of the finitely many closed oriented singleton loci below N is an open neighbourhood of the diagonal point, and f has norm less than epsilon there by the symmetry of the norm and the tail bound. This is the metric neighbourhood definition of continuity, so it needs neither a uniform-limit theorem nor a completeness assumption. I used this direct version to avoid silently applying a completeness-dependent result. The finite exclusions and epsilon estimate are written out.

Step 3 is a finite additive cancellation: on a singleton the potential is zero; on a double fibre it is 0 and a_k. The four ordered pairs give f(s,t)=u(t)-u(s), then the three displayed differences cancel. The local potentials need no continuity, and the proof never asserts that their union is a continuous primitive. This handles repeated entries of a triple, both orientations and additive characteristic two (where minus a_k equals a_k).

Step 4 cites only `lem-sfb-baire-closed-cover-interior`. I checked every hypothesis: E_n=g^{-1}(H_n) is closed because g is continuous and H_n is closed in A; the E_n cover T because the H_n cover A; the index is the countable set of natural numbers; T is nonempty and Hausdorff; T itself is a compact neighbourhood of every point, establishing local compactness. Apply the node with the whole subspace Y=T. Its nonempty-interior conclusion is precisely what the verbatim quote in citations.json says, giving the open U inside one E_j. No completeness of A is required for this use of Baire, which takes place in T.

Step 5 uses no extra theorem: tail density with N=j places a whole double fibre of index k>=j in U. Both g-values lie in the subgroup H_j, so their difference lies in H_j and hence H_k by the increasing-chain hypothesis. The oriented primitive equation makes this difference a_k, contradicting the stated escape condition. This explicitly checks the sign and the index comparison.

Small cases: the N=0 finite exclusion is empty and causes no problem; a_k cannot be zero because zero lies in H_k; singleton fibres give a zero cocycle; triples with repeated points still cancel; characteristic two needs no division or unequal signs. A finite or discrete coefficient group that cannot have such an escaping null sequence simply fails the hypotheses. The nonempty hypothesis is used exactly at Baire and the tail-density argument. No compactness or total-disconnectedness hypothesis is invented for A, and no completion, infinite sum, or closure of differences appears. The extra compact Hausdorff/totally disconnected assumptions on V and the total disconnectedness of T are harmless unused hypotheses retained from the item.

All elementary steps are short computations from the statement, and the sole non-elementary step has the precise existing node citation. No step exceeds 2000 characters; the original five steps totalled 2102 characters. The repair keeps every step below that threshold. No new nodes are elementary, duplicates, clauses renamed as lemmas, or missed Mathlib leaves because there are no new nodes. There are no off-unit proof citations, derived-object identifications, SGA citations, hollow definitions, circular references, or proof steps left unjudged. The statement dependency on the inherited size convention remains as in the live statement. The source and provenance distinguish the agent's analytic argument from the blueprint's motivation.

## Not duplicates

No new node pairs: no new nodes were created. The generic Baire leaf was reused.

## Unfinished work

No mathematical part of this one-level split is left unfinished. The existing Baire input is already a Mathlib leaf. Server dry-run and delivery results are recorded below once completed.


## Repair review by Q123 — 2026-10-23

1. **Return L: side completion not promoted to the live DAG.** The retained delivery log identifies the previously submitted content as `c190affbb6`. I continued those sandbox files rather than resetting them. I compared every field of the retained item with the current shared DAG: the live item is `unsplit`, with empty proof and proof dependencies, no review, and no released repair note. Its statement, statement dependencies, source, chapter, unit, blueprint ancestry and creation record agree with the retained item. The differences are precisely the completed proof, proof dependencies, proof origin, split status, split report and appended logged searches. The initial mandatory dry run completed successfully at `1d1cee6e5eb` against the current fetched DAG, confirming that the old content can be assembled on the current base. This delivery now includes an actual proof clarification and this repair review, not an unchanged re-push.

I re-read the current full statement of `lem-sfb-baire-closed-cover-interior`, its Mathlib-leaf record, and `def-weil-size-convention`. The Baire node still states exactly the nonempty locally compact Hausdorff closed-cover consequence quoted in `citations.json`, and still records `nonempty_interior_of_iUnion_of_closed` at Mathlib/Topology/Baire/Lemmas.lean:257 and the locally compact Baire instance at Mathlib/Topology/Baire/LocallyCompactRegular.lean:23. I opened both declarations and Stacks topology.tex, Tag 0CQN, `lemma-baire-category-locally-compact`, including its nested compact neighbourhood proof. The size convention fixes the universes and changes none of the topological hypotheses. There is no changed cited statement requiring a replacement dependency. The existing citation quote remains verbatim in the current node.

I adjusted step 4 to instantiate the Baire node explicitly with ambient space and whole subspace both equal to T, index set the natural numbers, and closed sets E_n. The step now writes the pointwise covering argument using g(t), identifies the whole-subspace topology with the given topology, and derives the openness and inclusion of U from the definition of interior. This makes all hypotheses and the precise conclusion used in step 5 visible against the current cited statement. Steps 1–3 still give the actual function, direct diagonal-neighbourhood continuity and finite fibrewise cancellation; step 5 still uses k>=j, both points in U, and subgroup differences to contradict a_k outside H_k. No completion, infinite sum, or completeness of A is introduced. The singleton-fibre, repeated-triple, N=0 and characteristic-two checks in the original review continue to apply.

I re-read the current chapter and recorded unit, paragraph (3) of the motivating main-20261015 direct-images proof, and delivery-errors B–E. This remains an agent-created analytic auxiliary, not a theorem stated in that blueprint paragraph. The proof uses only the existing Baire Mathlib leaf; no new node, off-route theorem, renamed clause, or hidden long-step lemma is introduced. The current project-source search by exact blueprint id, null-sequence, double-fibre and subgroup-exhaustion terminology gives no exact attachment. I read the retained five Q123 search results and the inherited Q46 records; neither the statement nor the search question changed, so I retained them and did not repeat or invent searches. No Lean files or build tools were used. The final delivery tool will rebuild and check this repaired content on the current DAG before pushing it.
