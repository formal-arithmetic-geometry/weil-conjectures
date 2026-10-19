Files written:
- `dag/nodes/sec-trace-formula/lem-trf-etale-regular-intersection-descent.json`: statement, split proof, no new Mathlib leaf.
- `dag/nodes/sec-trace-formula/lem-trf-etale-regular-local-invariance.json`: statement-only Stacks lemma, no Mathlib match.
- `citations.json`: verbatim statement quotes for every proof-step citation.

Attachments: none.

WANTED: none.

The item was not already proved by a sorry-free declaration in the read-only Lean source. The imported statement is mathematically sound, including the empty intersection case. The existing DAG already has `lem-sc-etale-local-dimension`, which is the dimension input for codimension; I did not duplicate it. The only new node is the genuinely separate regularity-invariance statement from Stacks Tag 025N.

## Review by NM
I read the item, its chapter and unit records, the source declaration search in `WeilConjectures/`, the imported blueprint ancestry, and the Stacks passages for Tags 025N, 039S, and 02GO. Step 1 uses the fibre-product and closed-immersion descriptions to identify the local base change, and the existing étale base-change node to obtain the induced étale map on the intersection. Step 2 applies the new node exactly to the Noetherian local rings `A/I` and `B/IB`; the hypotheses are met because the ambient schemes are locally Noetherian and the chosen point is local. Step 3 checks the generic-point setup for an irreducible component and uses only the elementary open-map/zero-dimensional-fibre property of an étale morphism. Step 4 applies the existing `lem-sc-etale-local-dimension` statement to the local rings at the two generic points, then unfolds the definition of Krull codimension. I checked `J=∅`, `n=0`, a single divisor, and a coordinate-hyperplane intersection; all give the expected codimension and regularity conclusions. No statement was weakened, no SGA source was used, and no cycle or duplicate was introduced.

## Not duplicates
lem-trf-etale-regular-local-invariance vs lem-trf-etale-regular-intersection-descent: the new node is the local algebra statement that a single étale map of Noetherian local rings preserves regularity; the item is the global scheme theorem simultaneously descending regularity and component codimension for every scheme-theoretic intersection.
