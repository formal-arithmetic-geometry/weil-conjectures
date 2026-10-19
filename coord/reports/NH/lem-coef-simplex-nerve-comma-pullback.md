# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-simplex-nerve-comma-pullback.json`: split the existing statement in five steps. No new nodes and no new Mathlib leaves. Searches found ordinary nerve, its quasicategory instance, comma categories, and nerve adjunctions, but no declaration combining the item's undercategory identification, isofibration, and Cat-infinity pullback assertions.
- `citations.json`: seven literal excerpts, one for every proof-step citation.

## Attachments

None. Searches for the item tag and for undercategory, comma, nerve and isofibration in the read-only slopmaster2 project found no project declaration stating every clause. The upstream master checkout is reference only.

## WANTED

WANTED: an archived copy of Lurie, *Higher Topos Theory*, Proposition 1.1.2.2, Example 1.1.2.6, Remarks 1.2.9.5-1.2.9.6, and Variant 4.2.3.15(5), for this item. Read online at https://www.math.ias.edu/~lurie/papers/HTT.pdf . No Stacks tag states this quasicategorical comparison. The proof is marked agent-written because it expands the missing elementary calculations and uses the existing generic pullback theorem.

## What was wrong and what changed

The imported node was statement-only. Its statement is retained verbatim, including all smallness, fullness, isofibration and specified-comparison clauses. The original source points to Proposition 4.1.1.8, which is a cofinality criterion; the direct source for ordinary slice nerves is instead Remark 1.2.9.6 and its undercategory dual (Remark 1.2.9.5). These precise sources are now given on the relevant proof steps. Variant 4.2.3.15(5), printed p. 256, uses the nondegenerate-simplex subcategory and Theorem 4.1.3.1, and is the parent application, not an explicit proof of this nerve comparison. No chapter or unit route is replaced.

I read the chapter, the assigned unit, the blueprint ancestor's current statement and proof, and the item's existing ancestry. The full-subcategory and simplex-comma calculations serve the existing HTT cofinal-poset replacement route in that ancestry. The item is not the unit key statement, so no unit realization field is changed.

## Review by NH

I read delivery-errors B through E and checked them against the final node. There are no new objects or statement-only child nodes to hide missing hypotheses or duplicate a clause. I searched DAG statements and blueprint references for undercategory and nerve comparisons; none gives the exact item. I read all four statement-dependency statements. The three proof interfaces retained are the ordinary nerve and coherent conventions, the definition of isofibration, and the full generic isofibration pullback-limit theorem. The comma criterion supplies the already stated coherent-under-category convention. All cited statements are quoted verbatim in citations.json; no proof of a cited node is used as an interface.

Step 1 uses the ordinary-nerve formula in def-cbc-enhanced-diagrams-cones. I checked the horn calculation dimension by dimension: composition in dimension 2, associativity in dimension 3, and presence of every triangle for n at least 4. This gives unique inner fillers. The inverse-triangle definition of equivalence becomes precisely an ordinary two-sided inverse. The countable union of X_n and finite ordinal map sets verifies smallness for C, B and the undercategory.

Step 2 uses the same nerve formula and the coherent-arrow convention from lem-coef-infinity-cofinal-comma-criterion. I checked the explicit inverse constructions: a join simplex is the string starting at sigma, and a fixed-source-arrow simplex is a functor from the grid [n] times [1] with its first row constant. Both amount to a target chain and equations h_j a_(j-1)=a_j. Restriction along an ordinal map retains a_(theta(0)) and composes the same arrows, so this proves an isomorphism over N(C), not merely an object correspondence. No general join-to-arrow equivalence is silently invoked; both models are computed here for an ordinary nerve.

Step 3 uses the nerve definition and the isofibration definition actually present in lem-coef-infinity-isofibration-exponentiation. Unique inner fillers from Step 1 make the filler automatically lie over the specified bottom simplex. An ordinary isomorphism e lifts by postcomposition from a to ea and has inverse e inverse in the undercategory. The two triangle equations verify an equivalence lift. Thus no non-elementary claim that arbitrary nerve functors lift equivalences is assumed, and the exponential-corner theorem itself is unnecessary.

Step 4 uses only the nerve formula and the fullness assumption of B. A strict compatible pair of target and undercategory chains is exactly a chain of pairs in sigma-downarrow-B; the maps and all simplicial operators agree. Step 5 uses precisely the statement of lem-coef-infinity-isofibration-pullback-limit. I checked its hypotheses: all three nerves are small quasicategories, q is the isofibration just proved, and no fibration condition on N(i) is needed. Its constant-path comparison gives the required specified homotopy pullback square after the preceding projection-preserving isomorphisms.

For edge cases I tested B empty (empty comma and empty pullback), B=C (the undercategory), X empty (no sigma, so the universal assertion is vacuous), X a point, and X a non-quasicategory such as a simplex boundary. The proof works for these because it uses only the ordinary category of simplices. The undercategory is never empty when sigma is supplied: it contains its identity. I corrected a draft sentence which had incorrectly suggested this undercategory might be empty, replaced paraphrased citations by literal TeX excerpts, removed the unnecessary exponential-corner argument, and distinguished two initial greps with an extra Mathlib path prefix from valid source searches. The latter were rerun at valid subdirectories and their actual outputs are recorded.

## Not duplicates

No new nodes were created. The item's own clauses are proved inline, not renamed as children. The existing generic isofibration pullback-limit node is cited for its theorem, not duplicated.

## Long-step review

The final proof-step lengths are 1120, 1054, 790, 765 and 922 characters. The first four are direct calculations from definitions (horns/composition, chains and operator restrictions, a lift and inverse, and compatible tuples); the last applies the already existing generic pullback theorem. No step hides a standard lemma with its own extra hypotheses.

## Unfinished work

None in this one-level split. The cited existing nodes remain their own separate DAG items. Dry-run and push results are reported by the delivery tool.

## Continuation review, 2026-10-17

The resumed worker retained the earlier proof, report, citations, and complete searches.jsonl, and started with the required dry run. Comparison against the current shared item confirmed that the statement, source, statement dependencies, creation record, chapter, unit and blueprint ancestry are unchanged. All seven excerpts in citations.json remain literal substrings of the current cited statements. The full ordinary-nerve and fixed-source-grid calculations were reread; in the inner 3-horn case the omitted triangular relation follows from associativity without cancellation, and in degrees at least four every triangle is present. The explicit isomorphism lifts need no equivalence-lifting property of an arbitrary nerve functor. The final theorem is applied with exactly its three small-quasicategory hypotheses and the projection isofibration, with its specified constant-path comparison.

I reread the online HTT sections 1.1.2 and 1.2.9 and Variant 4.2.3.15(5), the current dependency statements, the chapter and unit records, and the blueprint ancestor in both the master and main snapshots. Project-source searches again found no exact attachment. Existing slice-arrow and join-slice comparison nodes concern general quasicategories and do not replace this direct ordinary-nerve computation. Searches already logged were reused after reading their saved outputs; no Mathlib searches were repeated. I corrected only search-result summaries to the exact logged result objects and explicitly marked the rejected Loogle pattern as unavailable; the successful second Loogle query remains recorded. No mathematical statement or proof step needed repair, and no new node was created. All proof steps remain below 2000 characters. The archival HTT request above remains for the maintainer because literature/ is read-only to this worker.
