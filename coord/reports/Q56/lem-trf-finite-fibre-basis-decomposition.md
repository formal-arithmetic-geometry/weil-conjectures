# Stage-1 report: lem-trf-finite-fibre-basis-decomposition

## Files written

- dag/nodes/sec-trace-formula/lem-trf-finite-fibre-basis-decomposition.json: existing statement, split; no exact Mathlib match.
- citations.json: the sole cited node, in step 2, with its statement quoted verbatim.
- report.md: this report.

No new nodes, no Mathlib leaves, no unit or chapter edits. Searches were run with the prescribed msearch.py command and their returned results read. The existing Q142 searches in the item are preserved; the seven Q56 searches in searches.jsonl are appended exactly by tool and query.

## Attachments

None. The blueprint-tag and notion searches in lean/WeilConjectures found no declaration asserting every clause. The project uses mapDomain and sum_fiberwise in other calculations, but these uses are not declarations of this item.

## WANTED

None. The item's listed Mathlib supporting source is available locally. This proof is explicitly agent-written; no claim is made that a Stacks tag or the blueprint states the complete decomposition.

## Problems found and changes

The item was unsplit, with no proof or Lean attachment. Its statement is correct and unchanged. Its source only supplies the supporting coefficient formula, not the whole decomposition; the proof_origin now states this clearly. The dependency on def-weil-pbc-free-module is retained and used for the uniqueness of coordinates in step 2.

The entire proof consists of finite reindexing, linearity, coordinate evaluation and distributivity. These arguments are written out rather than split into new elementary nodes. The latest blueprint ancestor lem-trf-local-term-locality and the latest sk-i-curve-zero statement were read. They concern local terms; this is a commutative-algebra input deep in their chart-spreading ancestry, not a restatement of either. No route change or SGA citation is involved.

## Not duplicates

No new nodes are proposed. Full-DAG searches for mapDomain, fibre coefficients, basis vectors and representative subtraction led to this item, its congruence-kernel parent and algebra/sheaf results with different conclusions. Blueprint searches for mapDomain and basis vectors returned no matches. The parent proves an ideal-kernel formula, whereas this item proves the finite-module calculation that parent cites.

## Review by Q56

I read Mathlib/Data/Finsupp/Basic.lean at mapDomain_single (309–310) and mapDomain_apply_eq_sum (1432–1434), the item's supporting source. The coefficient theorem uses the actual support, while our arbitrary finite T may contain zero coefficients; the proof therefore evaluates the displayed sum directly and does not silently identify T with the support. I also read lmapDomain_disjoint_ker (Supported.lean:247 onward), whose injectivity-on-a-subset hypothesis does not hold here, and the fibre grouping in the proof of KaehlerDifferential.range_kerCotangentToTensor (Kaehler/Basic.lean:812 onward), which concerns a different map. The second semantic phrasing returned affine weighted-subtraction results; I read weightedVSubOfPoint_apply and the base-point independence calculation in Combination.lean. They support the elementary algebra but do not give this whole statement in one specialization. The item remains split, not a Mathlib leaf.

Step 1 has no external lemma: the two explicit inverse maps identify the finite indexing sets, and image membership supplies nonempty fibres. Representatives are required only for z in the finite image C. This verifies that no surjectivity of q, finiteness of X or Y, or nonzero coefficient assumption is used.

Step 2 cites only def-weil-pbc-free-module. I read its whole statement: it says every vector has a unique finite basis expansion, exactly the uniqueness used here. The step also writes coordinate evaluation explicitly, using the basis values defined in the item. Its citation quote is copied from that node's statement. The pushforward calculation follows from the map's stated linearity and basis values, and the reindexing was proved in step 1; it does not invoke an uncited pushforward theorem.

Step 3 expands every summand and combines the repeated e_{r_z} term using distributivity. It uses only the module axioms; no independence, division, cancellativity of a monoid, or integral-domain hypothesis enters. Step 4 sums that equality over the same finite partition, then inserts precisely the coefficient vanishing from step 2. The equality q(x)=q(r_z) follows from the two memberships in T_z. There are no further cited nodes to quote. All four steps are shorter than 2000 characters and have no hidden comparison or existence lemma.

I tested T empty (including X empty), singleton T, injective q, constant q, arbitrary zero coefficients in T, and the zero ring. For constant q the sole correction is (sum a_x)e_r; for injective q each difference is zero and the correction recovers f. Over Z/6, coefficients 2 and 4 on one two-element fibre give zero pushforward and the same subtraction identity; the argument does not require a domain. Representatives with zero coefficient also cause no problem, since membership in T_z, not support membership, is the only condition. The zero ring has every coefficient and basis function equal to zero, so all identities still hold. No statement dispute was needed.

I checked delivery-errors B–E against the node: no new incomplete nodes or duplicated facts; all notions introduced and the sole definition dependency read; no extra hypotheses, cycles or off-route statement tools; no clause moved into another node; all non-elementary input exhausted by the cited definition and elementary equations explicitly proved. Nothing remains mathematically unfinished in this one-level split.

## Unfinished work

None. Required dry run and direct delivery follow; their results are recorded below when available.
