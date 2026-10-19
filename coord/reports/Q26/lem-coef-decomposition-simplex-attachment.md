Files written:
- `lem-coef-decomposition-simplex-attachment.json` — statement node, split; no new child nodes and no Mathlib leaf created.
- `citations.json` — verbatim citations for every node used by every proof step.

Attachments:
- None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the item id, its key phrases, and the blueprint tag; no sorry-free project declaration states this item.

WANTED: the HTT PDF at `https://www.math.ias.edu/~lurie/papers/highertopoi.pdf`, Notation 4.2.3.1, Remark 4.2.3.2, Notation 4.2.3.7 and Proposition 4.2.3.8 (printed pp. 248–252), for the decomposition attachment argument. The online source was read, but no archival copy is in the repository.

What was checked and corrected:
- The imported statement is unchanged. The proof now expands the characteristic map, classifies new simplices degreewise by the unique nondegenerate decomposition, and treats nondegenerate and degenerate base simplices separately.
- No duplicate node exists: `lem-coef-decomposition-local-colimit-cocones` defines the decomposition simplicial set but does not state an attachment pushout; `lem-coef-decomposition-simplex-lift-right-anodyne` uses this item and is strictly stronger/different. The Mathlib leaf `lem-weil-pbc-simplicial-set-nondegenerate-decomposition` supplies only unique degeneracy decomposition.
- I checked the edge cases $m=0$, empty $K$, empty $B$, and empty $D_\\sigma$. In particular, the proof retains the pure lower factor in $\\Delta^m\\star B_0$ when $B_0=\\varnothing$ and uses $\\partial\\Delta^0=\\varnothing$.

## Review by Q26

I read the item node, the chapter record, the `sk-prop-sf-biduality-general` unit record, and the existing statements of `def-cbc-enhanced-diagrams-cones`, `def-coef-infinity-relative-cone`, `lem-coef-decomposition-local-colimit-cocones`, and `lem-weil-pbc-simplicial-set-nondegenerate-decomposition`. Step 1 uses only the ordered-block and join definitions plus the exact operator clause in the decomposition node; it verifies that the displayed formula for $c_\\sigma$ is simplicial and lands in $L'_F$. Step 2 uses the Mathlib leaf's existence and uniqueness of a surjection to a nondegenerate root and the decomposition node's cut/lift description; this is the classification of all new simplices and explains why degenerate first lifts are precisely the old $B_0$ part. Step 3 applies that classification when $\\sigma$ is nondegenerate and checks the boundary join is exactly the old intersection. Step 4 repeats the check for degenerate $\\sigma$, verifying the intersection $\\partial\\Delta^m\\star B_0$ and the pure lower factor. Step 5 checks the boundary convention and empty-factor cases. Every cited statement was opened and the quoted text in `citations.json` is verbatim. I ran the four required Mathlib searches for this item and recorded their results; none states the attachment lemma. No hypotheses were added or dropped, and no SGA source was used.

## Not duplicates

No new nodes were created, so there are no new-vs-existing duplicate pairs to report.

What I could not finish:
- Nothing remains within the authorized stage-1 split. The external HTT source remains listed as WANTED because it is not archived in the repository.
