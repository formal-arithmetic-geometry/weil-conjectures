# Q156: lem-sfb-shuffle-horizontal-face-reindexing

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-shuffle-horizontal-face-reindexing.json`: statement item, now split into eight elementary counting steps; not a Mathlib leaf. Statement, statement dependencies, created record, source record, and inherited blueprint fields preserved; added proof, origin, searches and split report.
- No new nodes; no Mathlib leaves added.
- `citations.json`: the single proof citation, at step 8, with a verbatim excerpt of the free-module definition.
- `searches.jsonl`: actual msearch records; six fresh searches, including a second semantic phrasing.
- `check_small_cases.py`: finite combinatorial verification; no Lean and no compiler.

## Attachments

None. Searched all `lean/WeilConjectures/` for the exact blueprint id and for `shuffle|Shuffle`. There is no id hit. The two conceptual hits are a categorical braiding/evaluation identity in `Algebra/Category/ModuleCat/Sheaf/FiniteProjectiveInternalHomEvaluation.lean:92` and a complementary exterior pairing in `RingTheory/KoszulComplementaryEquivalences.lean:74`. I read both: neither concerns marked word faces. Thus neither is an attachment. No repair note exists for this item.

## WANTED

WANTED: Weibel, *An Introduction to Homological Algebra*, §8.5, for lem-sfb-shuffle-horizontal-face-reindexing (already requested by the inherited source record). I did not use an unavailable text as proof evidence; the proof is explicitly agent-written.

## What was wrong or missing

The item was a correct but statement-only combinatorial input; it had no proof. No statement correction is needed. The latest blueprint direct-images proof paragraph (3) gives the direct-image application, not a shuffle calculation. The source field already acknowledged this. I retained that provenance and used `proof_origin.by = agent` with the latest blueprint application as context. No claim is made that Stacks or the blueprint states this lemma, and no SGA reference is used.

The recorded unit `sk-thm-sf-ctf-stability` is the inherited unit. Its stored unit record has chapter `sec-six-functors`, while the item's inherited chapter and source location are `sec-six-functors-basics`. I read both the chapter and unit and have not changed this inherited metadata or their route. This is a lower-level explicit calculation in the existing shuffle argument; no unit realization field needs editing. `blueprint_refs.py ancestor` returns None. I preserve `from.node = null` and the existing via chain, and explain the precise parent-proof place in the split report.

## Search results and duplicates

Read the whole-item inherited searches, then ran all four required services under this group and item. Loogle `"shuffle", "face"` and the targeted grep return zero hits. LeanSearch returned simplicial path vertices and graph vertex/edge deletions. The first LeanFinder returned path restrictions and simplex degeneracy normal forms. A second phrasing about deleting an equal letter returned Coxeter word products/inverse sequences and Dyck nesting. The broader Combinatorics grep returned quiver reversal and incidence-algebra Möbius inversion. These results concern different statements and objects: none identifies marked horizontal faces with shorter shuffles while giving the input-sequence deletion identity, endpoint inversion counts and signs. I read the relevant path and simplex normal-form declarations in Mathlib; they cannot specialize to the whole item in one line. Exact queries and tool output digests are in the log and node, with no invented search.

Whole-DAG keyword searches found this item and its parent, and the mixed-corner and vertical companion lemmas. They do not replace this item: the parent cites it and cannot be used without a cycle; the companions concern the other face types. Whole-blueprint searches for `shuffle` and `horizontal face` returned no same-as node. No node is created, so there are no new-node duplicate pairs or elementary subclaims incorrectly promoted to nodes.

## Review by Q156

I read `coord/brief-stage1.md`, stage 1, GOAL, the three SETUP levels, the worker contract, and both occurrences of delivery-errors B–E. For the source I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md` paragraph (3), together with the parent shuffle-boundary node and its review. This source only motivates the use; the proof below is my direct finite counting argument. There are no new nodes needing independent sources.

Steps 1–2 cite no nodes: removing a horizontal letter gives the asserted counts, and splitting the i-th surviving H gives both inverse identities. I checked the index is one-based for that H and the vertex mark is zero-based, k=|P|+1; the inverse really recovers the mark, not just the word. The inequalities 0<i<a guarantee that this H exists. The endpoint labels are disjoint because a>0.

Steps 3–4 cite no nodes: the two prefix-count formulas compare every remaining vertex with its original index r or r+1. In the interior, before the mark the horizontal prefix is below i; after it the old horizontal prefix is above i, so deleting u_i restores exactly the right coordinate. The endpoints use (d_0 u)_h=u_{h+1} and (d_a u)_h=u_h for h<a. The vertical coordinate is unchanged. These are direct substitutions into the item's definitions and do not invoke any simplicial theorem.

Steps 5–6 cite no nodes: I explicitly partitioned inversion pairs into retained pairs and those involving the removed H. At an interior HH I remove the second H, so precisely B_k vertical letters precede it. Initially none precedes it, terminally all b do. No extra permutation-sign theorem is needed. The partition of a prefix gives k=i+t.

Step 7 cites no nodes: substituting the counts makes the exponents differ by 2t or 2b. The sign equality is ordinary integer power arithmetic, with the initial case k=i=0.

Step 8 cites only `def-weil-pbc-free-module`. I opened its statement: it defines a basis by unique finite linear expansion. That is exactly what is used to interpret equal strings as equal basis symbols; it is not used as a combinatorial or sign theorem. The quote in citations.json is verbatim. I checked a=1 has no HH interior, b=0 gives zero inversion counts, a=1,b=0 has two differently marked endpoints of the same word and a single empty shorter word, and a=0 has no admissible horizontal mark (including the empty word). Repeated entries only identify evaluated strings, never the labeled pairs. This is why no distinctness hypothesis enters the inverse argument.

I ran `check_small_cases.py` on every shuffle with 0<=a,b<=6. It verifies both inverse identities and target coverage, all inversion and sign formulas, and evaluated deletions using distinct entries, constant entries, and alternating repeated entries. Each proof step is below 2000 characters. There are no hidden non-elementary comparisons or uncited external facts, no new unsplit nodes containing proofs, no relabelled clauses, and no dependency cycle: the only proof edge goes to the existing Mathlib free-module definition. All hypotheses and the full original statement are retained.

## What remains unfinished

Nothing in the requested stage-1 split. Lean formalization is outside the authorized scope. Server dry run and direct delivery are the remaining operational checks.
