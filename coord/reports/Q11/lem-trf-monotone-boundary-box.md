## Files written

- dag/nodes/sec-trace-formula/lem-trf-monotone-boundary-box.json: existing statement, now split into four elementary steps. Mathlib verdict: no exact match or one-line specialization found.
- citations.json: empty list, because no proof step cites another node. The existing statement dependency def-weil-pbc-mv-polynomial-ring is retained.
- No new nodes and no new Mathlib leaves. searches.jsonl contains the actual new search-command results; the item's pre-existing search records are preserved.

## Attachments

None. Searches in lean/WeilConjectures for the blueprint tag, monotone diagrams, monomial boundaries and the boundary-box notion found no declaration stating this result. Unrelated monotone filtrations do not qualify. No Lean was written or compiled.

## Wanted literature

WANTED: Bierstone--Milman, Canonical desingularization in characteristic zero by blowing up the maximum strata of a local invariant, Inventiones Mathematicae 128 (1997), section 8, Lemma 8.2 and Remarks 8.4, pp.274--275, for lem-trf-monotone-boundary-box. This paper is absent from the repository literature. I did not download it or claim to have read it. The elementary proof here is written by the agent, and does not invoke any theorem from that paper.

## Corrections and source assessment

The item's statement and statement dependency are unchanged. There is no statement dispute. The source field already describes this as an agent combinatorial refinement, rather than a theorem appearing in ILO. I read ILO VIII 2.3.11--2.3.13, printed pp.93--94 (PDF pp.99--100): these discuss functorial desingularization and its historical alternatives, and do not state the quantitative box bound. Accordingly proof_origin.by is agent, and each step's source explicitly distinguishes the historical context from the coordinate proof.

I read the current latest blueprint's lem-trf-local-term-locality statement and proof, and the item's chapter and unit records. The current ancestor uses contracting correspondences; the recorded ancestry of this auxiliary item is historical. I also read the full live split of lem-trf-monotone-diagram-face-exceptions: its Steps 2 and 3 apply exactly this unchanged boundary lemma to an earlier-vertex prefix and to the whole diagram. This delivery proves the assigned auxiliary input, without changing the unit or its route. The item is not the unit's key statement, so no unit record is delivered.

## Not duplicates

No new nodes. Whole-DAG phrase searches for coordinate boundaries and monotone upper sets found this item, its face-exceptions parent, the vertex-prefix input and unrelated coordinate constructions. Whole-blueprint searches via tools/blueprint_refs.py for monotone, boundary bound and monomial found no equivalent blueprint statement. The vertex-prefix result concerns preservation of monotonicity for prefixes, whereas this item assumes monotonicity and bounds a boundary. The parent depends on this item; it is not used in this proof.

## Review by Q11

I checked sections B through E of delivery-errors.md against the written item. The argument never uses a cited node's proof or an unstated geometric result. All four steps have uses=[] and elementary=true: they are direct consequences of the explicitly displayed union of orthants, the assumed transfer, and finite sums of nonnegative integers. There are consequently no citation quotes to certify, and citations.json is []. I read def-weil-pbc-mv-polynomial-ring's statement; it defines precisely the monomial exponents mentioned in the item and is needed only to state that contextual identification, not to prove the coordinate inequalities.

Step 1 expands membership as existence of a dominated generator and proves upward closure explicitly by coordinate subtraction. It assumes neither a minimal list of generators nor Dickson's lemma. Step 2 chooses the generator only after v+e_k is assumed to lie in U. Coordinates other than k are already bounded by v; if the k coordinate were also bounded, v would lie in U. Integrality therefore forces the equality a_k=v_k+1. The inequality a_k<=|a|<=M gives v_k<M without any monotonicity assumption.

Step 3 is the only place using whole-coordinate monotonicity. It applies it to the generator a itself, which Step 1 puts in U, with p=k and t=j>k, exactly the direction authorized in the hypothesis. The transferred vector has kth coordinate zero and jth coordinate a_j+a_k. The indices are distinct, so the latter is at most |a|, not a double count of one summand. If v_j>=M, every coordinate of this transferred vector is at most the corresponding coordinate of v. Upward closure then contradicts v outside U. I wrote this comparison out rather than hiding it behind a transport or standard-lemma claim. It has no independent non-elementary subclaim to extract.

Step 4 checks A empty, U full and k=n; n=1 follows from k=n. For M=1, the same arithmetic says every required coordinate is zero. No condition of minimality or degree ordering of A was introduced. As an additional finite check, I enumerated all generator subsets with total degrees <=M for (n,M)=(1,3),(2,3),(3,2), retained those stable under every generator transfer, and checked v in {0,...,M+1}^n. This covers 1549 stable generator families and 2278 entering boundary pairs; both witness and all coordinate bounds held. Testing stability on generators is valid here because the transfer is additive, preserves coordinatewise inequalities, and U is their upward closure. The written proof, not this finite check, establishes all n and M.

I read the actual signatures returned by LeanFinder (both phrasings), LeanSearch and Loogle, plus the logged grep results. Upper-closure boundedness is a lower bound on a whole upper set; polynomial degree bounds and Chevalley complexity functions do not give a boundary estimate under coordinate transfers. None is a leaf for this item. Queries and result summaries were copied from searches.jsonl without inventing searches. Every proof step is below 2000 characters (336, 357, 498, 314); no long step hides a lemma. No SGA route or source is used.

## Unfinished work

None in the assigned split. Independent maintainer review remains after delivery.
