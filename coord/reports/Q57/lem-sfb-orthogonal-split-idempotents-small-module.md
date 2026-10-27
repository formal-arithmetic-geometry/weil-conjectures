# Q57 stage-1 worker report

Item: `lem-sfb-orthogonal-split-idempotents-small-module`.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-orthogonal-split-idempotents-small-module.json`: statement item, now split; no whole-item Mathlib match. Four proof steps, citing existing nodes only.
- `citations.json`: three verbatim statement citations, for steps 2, 3 and 4.
- `report.md`: this report. `searches.jsonl` is the search command's original log, retained without editing.

New nodes: 0. New Mathlib leaves: 0. The already existing `lem-sfb-independent-family-spanning-cardinality` is a Mathlib leaf and is reused, not redelivered.

## Attachments

None. Searched the live project `lean/WeilConjectures/` both for the item id/docstring tag and for orthogonality, idempotents, and countability/independence terminology, including the likely LinearAlgebra and SixFunctors directories. No project declaration states all the item's clauses. In particular the parent's sorry declaration is not a proof of this item and no attachment is claimed from `Sheaf/`.

## Wanted literature

WANTED: an external reference for the split-idempotent independent-family calculation in this item, especially with products assumed zero only as operators on the module; the item's existing source explicitly asks for it. The agent proof is supplied completely in the node, rather than attributed to a nonexistent theorem of the blueprint. The cardinality result does have an exact source: Mathlib's `linearIndependent_le_span''` in `Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean`, lines 287–299, declaration at 290.

## Audit of the imported item and route

No statement error was found; the statement, statement dependencies, original provenance, inherited search records and blueprint chain are preserved. The initial item had no proof. The current blueprint's direct-images proof paragraph (3) treats proper and open direct images; it does not itself prove this extracted coefficient auxiliary. I read that paragraph and the parent reconstruction split: its quotient has a unital algebra action and its distinct projection products kill the quotient, which is precisely the action-level hypothesis used here. The present proof does not silently strengthen it to a product identity in the algebra. The unit and chapter records were read; this algebraic auxiliary stays below the same coefficient argument, and no unit route or realization field changes.

The blueprint ancestor command returns `None`, consistently with the inherited null ancestor. Whole-blueprint searches for `split idempotents`, `orthogonal idempotents`, `linearly independent`, `spanning cardinality`, and the combined cardinality/injection phrase found no equivalent blueprint statement. The three results for `split idempotents` concern other categorical idempotent splittings, not independent translates in arbitrary modules. Whole-DAG keyword searches found the exact existing spanning-cardinality leaf, which I opened and reused. No new elementary, duplicate, clause-restating, or already-Mathlib node was created.

## Search findings

Retained all six inherited Q36 searches. Six new searches were run by the prescribed msearch.py command and their original result objects are appended from searches.jsonl. Loogle and the idempotent/independence grep found no match. LeanSearch's bilinear/sesquilinear and inner-product orthogonality results need extra structures absent here; I read the source statements at SesquilinearForm/Basic.lean:121–122 and BilinearForm/Orthogonal.lean:122–123. Both LeanFinder phrasings returned spanning-cardinality and finite-span results, which assume linear independence and therefore do not prove the action calculation. The broader grep also returned the dimension file. I read `linearIndependent_le_span''` at 290–299: it accepts an arbitrary independent family and a set whose span is top, under StrongRankCondition, available for a field. This is exactly the already-existing leaf's statement, not the full item. No service was unavailable and no unrun query has been added.

## Not duplicates

No new nodes. The existing spanning-cardinality leaf supplies the non-elementary input to step 3. The item additionally derives independence from split operators and includes the countability consequence, so it is not a restatement of that leaf. No same-Stacks-tag pairs are introduced.

## Review by Q57

I read coord/delivery-errors.md B–E in full and checked the concrete four-step proof against each applicable point. For the item I read the current blueprint direct-images paragraph (3), the parent's reconstruction proof, and all three cited node statements; for the cardinality input I also read the actual Mathlib source, and for countability I read Data/Countable/Defs.lean:39–47. There are no new nodes needing separate sources or searches. The absence of an external proof for this extracted auxiliary is recorded above and the proof origin is explicitly agent, so the source reference does not pretend to prove what it only motivates.

Step 1 has no node citations: r_i u_i=1 gives r_i x_i=q and p_i x_i=x_i by associativity. Crucially, p_i x_j=(p_i p_j)x_j uses the zero-action hypothesis at x_j, which is an element of Q; it does not cancel a factor inside D or require faithfulness. This is a few-line module calculation. Step 2 uses def-weil-field only for inversion of a nonzero coefficient, which its statement explicitly supplies. The induced scalar structure means elements of D act K-linearly because the image of K is central. Applying p_k to a finite relation leaves one summand; applying r_k then gives t_k q=0, and multiplying by t_k inverse is valid if t_k is nonzero. Thus the entire independence assertion is proved in the steps rather than relabelled as a new lemma. Both calculation steps are elementary in exactly the few-line sense of the brief.

Step 3 uses the statement of lem-sfb-independent-family-spanning-cardinality, not its proof. I checked each hypothesis: K is a field; Q is the induced K-vector space; step 2 gives finite-relation linear independence for the entire I-indexed family; W spans Q by hypothesis. The cited statement explicitly concludes existence of an injection into W and allows arbitrary sets with universe lifts. Its statement dependencies do not lead back to this item, so this edge is not circular. Step 4 cites def-sfb-countable-set, whose statement defines countability by an injection to the natural numbers. Composing its injection with that of step 3 is explicitly shown injective. No dimension theorem, hidden basis construction, or separate cardinal arithmetic result is used in this step. Every citation has a verbatim quote in citations.json, checked against the opened node statements.

I tested Q=0 (the first two clauses are conditional/vacuous), I empty (empty independence and the empty injection), I a singleton (only r_i u_i=1 is needed), finite relations with empty support, and W empty (if it spans, Q=0, so the nonzero conditional never applies). The proof works in positive characteristic and for noncommutative D; it uses only the central K-scalars, the unital module laws, and the action-level orthogonality. It assumes neither a norm nor completeness nor a faithful action. No statement correction, strengthened hypothesis, weakened conclusion, hollow definition, SGA source, off-unit non-tool citation, or proof step longer than 2000 characters is introduced. The only substantive improvement is supplying the previously empty proof while reusing the existing cardinality node.

## Unfinished work

None in this stage-1 split. No Lean files were written and no compiler, Lake, or build command was run. The required server dry run and delivery result are recorded by the delivery tool.
