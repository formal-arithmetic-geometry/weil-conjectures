# Delivery report

1. Files written:
   - `dag/nodes/sec-curve-estimates/lem-sc-conductor-ideal-restriction.json` — statement, split proof in two steps; no new nodes; no Mathlib leaf.
   - `citations.json` — verbatim statement excerpts for every cited node and step.
   - `report.md` — this report.
2. Attachments: none.
3. WANTED: none; the Stacks source is available at Varieties Remark 09NW.
4. The item was unsplit. I added the existing `lem-sc-conductor-ideal-zero-intersection` and `def-pc-module-pullback` dependencies, then stated the affine-open kernel/image argument and the product-versus-intersection argument. No statement or source error was found.
5. Nothing remains unfinished.

## Review by K1

I read the item node and the existing `lem-sc-conductor-ideal-zero-intersection` node in `dag/nodes/sec-curve-estimates/`, and read Varieties Remark 09NW in `/home/ubuntu/c1-stacks-review/varieties.tex` (the imported source path is `literature/stacks-project/varieties.tex`, tag `varieties-remark-conductor`, 09NW). The remark says for a reduced ring that $I\\cap J=0$ and that $IB=I/(I\\cap J)$; this is exactly the algebra used in both steps.

Step 1 cites the zero-intersection node for the hypothesis $\\mathcal I(U)\\cap\\mathcal J_1(U)=0$, the closed-immersion ideal-sheaf definition for the kernel description, and the pullback definition for the image sheaf $\\mathcal I_1$. Those cited statements contain precisely the facts used. On each affine open, the restriction map has zero kernel and image defined to be $\\mathcal I_1$, so it is bijective; the affine-local criterion gives the sheaf isomorphism. Step 2 cites the same zero-intersection statement and the ideal-sheaf definition; the inclusion $\\mathcal I\\mathcal J_1\\subseteq\\mathcal I\\cap\\mathcal J_1$ is the elementary product/intersection inclusion, hence both are zero. I checked the edge cases $r=1$ (then $\\mathcal I=\\mathcal O_Y$ and $\\mathcal J_1=0$) and two reduced components meeting in a node (the local model $k[x,y]/(xy)$ with $I=(x)$ and $J_1=(y)$), where the equalities hold.

The existing node was searched before citation; no duplicate node was created. Mathlib searches recorded on the item (LeanSearch, LeanFinder, and Mathlib source grep) found no conductor restriction theorem, so the item remains a split statement rather than a Mathlib leaf.
