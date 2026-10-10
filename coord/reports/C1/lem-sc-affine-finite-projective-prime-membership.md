1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-affine-finite-projective-prime-membership.json` (statement, split into two proof steps).
- `dag/nodes/sec-curve-estimates/lem-sc-free-prime-membership.json` (statement-only child; Mathlib searches found no exact match).

2. Attachments: no Lean declaration matched the item tag or statement in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`.

3. WANTED: none.

4. What was checked and corrected: the item statement was read together with its blueprint ancestor `lem-sc-pic-proper-ntorsion` and the existing projective-module and localization definition nodes. I searched the whole DAG and blueprint for the localization membership criterion and found no existing node. The returned direct-summand child was deleted because it restated the item and was conditional on the item. The free child was rewritten with TeX and with an explicit module localization $F_{\\mathfrak p}=S^{-1}F$, $S=R\\setminus\\mathfrak p$; its statement is now self-contained. Step 1 now says that finiteness gives a surjection $R^n\\twoheadrightarrow N$ and that the lifting clause of `def-weil-pbc-projective-module` gives $i$ with $\\pi i=1$. Step 2 explicitly applies $i_{\\mathfrak p}$, invokes the free criterion, applies $\\pi$, and proves the converse by the canonical localization map. I checked edge cases $N=0$, $N=R$, $N=R^2$, and $s=0$; all give the stated equivalence. `citations.json` records verbatim quotes for every cited node in each step.

5. What I could not finish: the two child statements remain unsplit natural-language leaves because no single Mathlib declaration states either combined criterion; they are queued for later proof work as required by stage 1.

## Review by C1

I checked the Stacks source cited for Tag 00NX and the blueprint ancestor route, and opened the exact statements of `def-weil-pbc-projective-module` and `def-weil-pbc-localization-at-prime`. The item has no declaration or sorry-free attachment in the Lean checkout. For step 1, the projective definition says every map from a projective module lifts along a surjection; together with finite generation this gives $R^n\\twoheadrightarrow N$, and the resulting $i$ and $\\pi$ are the maps used later. For step 2, the projective definition's direct-summand clause supplies $\\pi i=1$, while `lem-sc-free-prime-membership` says exactly that free-module membership in $\\mathfrak pR^n$ is equivalent before and after localization. I verified that each cited statement contains the quoted fact in `citations.json`, and that the hypotheses (commutative ring, prime ideal, finite projective module, and finite free presentation) match at the relevant step. The projection calculation is elementary once those statements are available; the only non-elementary input is the free criterion. I checked $N=0$, $N=R$, $N=R^2$, and $s=0$. The repair specifically removes the item-restating child, adds the missing finite-generation/lifting explanation, fixes the module-localization notation and TeX, and records the actual citation review.
