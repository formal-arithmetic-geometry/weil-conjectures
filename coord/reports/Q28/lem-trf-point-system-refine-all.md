# Worker report: lem-trf-point-system-refine-all

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-point-system-refine-all.json` — item split into four proof steps; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-point-system-refine.json` — statement-only one-cover support node; no Mathlib match.
- `citations.json` — verbatim citations for every proof-step dependency.

## Attachments

None. I searched the available `WeilConjectures` source trees for the item id, Tag 00YP, and `lemma-refine-all-at-once`; no sorry-free project declaration states this item or the new support statement exactly.

## WANTED:

None. The complete Stacks source is present at `literature/stacks-project/sites.tex`.

## What was wrong or corrected

The imported item had no proof split. I added the genuine one-cover lemma from Tag 00YO as a smaller statement-only node, then split Tag 00YP into the well-ordered recursion over all finite-covering/map pairs. The support node is strictly smaller: it handles one fixed cover and one fixed element, while the item handles every such pair simultaneously. The item’s statement and hypotheses are unchanged. The DAG search found no existing node stating Tag 00YO or 00YP; generic filtered-colimit and site nodes are cited where their statements supply the needed facts. The Mathlib search services returned only generic inverse-system, direct-limit, and site infrastructure, with no exact refinement theorem.

## Review by Q28

I read the item, the `sec-trace-formula` chapter, unit `sk-i-curve-zero`, the nearest blueprint ancestry, and the complete proofs of Tags 00YO and 00YP in `literature/stacks-project/sites.tex`. Step 1 uses the site definition for the set-valued covering data and the colimit definition for the system and its colimit functors. Step 2 applies the exact statement of the new one-cover node at each successor stage of a well-ordering of all pairs; its hypotheses are the current directed system, the same distinct colimit sections, and one finite covering/map pair. At limit stages I explicitly take the union of the nested systems and check directedness and transition-map compatibility.

Step 3 uses the existing filtered-colimit elementwise statement for equality: any alleged equality in a union colimit is witnessed at a later index already belonging to one earlier stage, contradicting that stage’s distinctness invariant. Step 4 uses the same node’s representation clause to place every finite-cover/map pair at its processing stage; the factorization then persists in the final union. I checked that all cited quotes in `citations.json` are literal substrings of the cited statements, that every proof dependency is listed, and that no step cites an internal proof rather than a node statement.

I tested the construction on a constant one-object system and on a two-member finite cover; the former reduces to the usual sheaf separation argument, and the latter selects one pullback member as in Tag 00YO. Empty-cover edge cases are vacuous because the item assumes distinct sections and a finite covering datum. All proof steps are below the long-step threshold and no statement is a restatement of the item.

## Not duplicates

lem-trf-point-system-refine vs lem-trf-point-system-refine-all: the support node handles one fixed finite covering and one fixed element of the original colimit; the item handles all finite-covering/map pairs simultaneously by transfinite recursion.

lem-trf-point-system-refine vs lem-trf-finitary-site-enough-points: the support node constructs a single refinement of a given inverse system, whereas the existing enough-points node iterates refinements to construct a conservative family of points and has a different conclusion.

