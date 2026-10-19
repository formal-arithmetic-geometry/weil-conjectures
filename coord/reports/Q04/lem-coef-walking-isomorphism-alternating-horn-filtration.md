# Stage-1 report: lem-coef-walking-isomorphism-alternating-horn-filtration

Files written:

- `dag/nodes/sec-six-functors/lem-coef-walking-isomorphism-alternating-horn-filtration.json` — existing item completed as a split statement; no new nodes and no Mathlib leaves.
- `citations.json` — four step-to-node quotations.
- `report.md` — this report.

Attachments: none. I searched `WeilConjectures/` in `/home/ubuntu/weil-src-slopmaster2` for the item id and for the walking-isomorphism/alternating-horn notions; no project declaration states this item, and the upstream master source is reference material only.

WANTED: an archival copy of Kerodon tag 00UG, Subsection 3.1.2 (Definition 3.1.2.1 and Remark 3.1.2.6), because only the online source was available. The proof is therefore recorded as agent-written while following that cited construction.

No statement error or source error was found. The imported statement is retained verbatim. No new node was created: the nerve word classification, the alternating face calculation, and the degreewise horn pushout are short consequences of the existing definition node `def-cbc-enhanced-diagrams-cones`, so making any of them a separate node would duplicate a proof step or restate a clause of the item.

Nothing remains unfinished in the split. The item has no Lean declaration and no Mathlib match; its existing searches were read and retained. The recorded searches report only generic nerve/horn/coherent-isomorphism declarations and no filtration theorem.

## Review by Q04

I read the item node, its fixed chapter `sec-six-functors`, its unit `sk-prop-sf-biduality-general`, and the complete statement of `def-cbc-enhanced-diagrams-cones`. I also read the parent node `lem-coef-walking-isomorphism-edge-anodyne` to verify what this item must supply, and searched the DAG and both read-only Lean trees for an attachment or duplicate. The item’s own Mathlib search records were checked: LeanFinder, Loogle, grep, and LeanSearch find generic nerve/horn/coherent-isomorphism APIs but no statement of this filtration.

Step 1 uses exactly the cited definition’s nerve clause, “For a small ordinary category $I$, its nerve $N(I)$ has $n$-simplices the functors $[n]\\to I$, with restriction as simplicial operators.” I checked that the chaotic two-object groupoid gives one word for each binary vertex sequence and that degeneracy is equivalent to a repeated adjacent vertex; hence the only nondegenerate words are the two alternating ones. Step 2 uses the same nerve clause and explicitly computes faces: an interior deletion creates an adjacent repetition, the last face is the forward alternating word of one lower dimension, and the first face is the opposite alternating word. This verifies the stated new simplices and all face hypotheses.

Step 3 uses the nerve classification from Step 1 and the cited definition’s exact horn clause, “The standard simplex $\\Delta^n$ has $m$-simplices the weakly increasing maps $[m]\\to[n]$; its operators are precomposition, and its horn $\\Lambda_i^n$ is the simplicial subset consisting of maps whose image omits some vertex other than $i$, equivalently the union of the faces other than the $i$th face.” I checked that the face map for $w_n^0$ defines the horn map into $J_{n-1}$, that only $d_0w_n^0$ is new, and that the degreewise pushout adds exactly that face and the top simplex with all its degeneracies. Step 4 again uses the nerve clause to identify the initial edge, show that every forward alternating word appears at its indexed stage and every reverse word is the first face of the next stage, and conclude that the union is all of $J$. Swapping labels $0$ and $1$ gives the reverse filtration. I checked the small cases $n=2$ and $n=3$ explicitly, including the new edges/faces, and found no missing hypothesis or unintended identification.
