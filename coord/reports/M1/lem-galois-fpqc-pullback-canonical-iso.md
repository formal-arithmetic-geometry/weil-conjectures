Files written:

- `dag/nodes/sec-curve-estimates/lem-galois-fpqc-pullback-canonical-iso.json`: statement, split proof, two existing definition dependencies; no new nodes; Mathlib no direct match.

Attachments:

- None. No sorry-free slopmaster2 declaration states this item exactly.

WANTED: `literature/stacks-project/descent.tex`, Tags 02VS and 023Y, for `lem-galois-fpqc-pullback-canonical-iso` (the repository contains the citation index but not the checked-out Stacks source).

What was wrong in the node, blueprint, or brief:

- The imported item was unsplit despite being cited by the reviewed refinement lemma. I supplied the missing proof steps; the statement already precisely introduced the descent-data category and pullback functors.
- No new node was needed after searching the whole DAG and blueprint. `def-pc-fibre-product` states the universal property, uniqueness, and functoriality of fibre products, while `def-pd-descent-datum` states the comparison isomorphism and cocycle condition.

What I could not finish, and why:

- The Stacks source file named by the imported citation is not present locally, so the proof is recorded as agent-written from the cited Tags and the existing definition statements.

## Review by M1

I checked the item against the existing `lem-galois-fpqc-refinement-fully-faithful` proof, which uses this comparison exactly for the maps `p` and `h \\circ q`. Step 1 uses the fibre-product node's functorial induced morphisms and the descent-datum node's isomorphism `pr_0^* V \\cong pr_1^* V`; these statements support pulling the comparison back along `(r_0,r_1)` and its naturality. Step 2 uses the descent-datum node's explicit cocycle identity, which is the required equality after the two further pullbacks. Step 3 uses the fibre-product node's unique-isomorphism clause for the canonical associativity identification and the descent-datum node's fibre-product pullback construction; the latter statement is cited only for the induced datum and morphism transport. I verified the hypotheses that all maps are over `S`, so `(r_0,r_1)` factors through `X \\times_S X`, and that the composition maps are over `S`. The small cases `r_0=r_1` and `t=\\mathrm{id}` reduce to the identity comparison by the descent datum and the universal property. The Mathlib searches already recorded on the item cover LeanSearch, Loogle, and source grep and found no direct scheme-level theorem. I corrected the previously empty proof and proof dependencies, set `status` to `split`, and recorded the blueprint place and citation quotes.
