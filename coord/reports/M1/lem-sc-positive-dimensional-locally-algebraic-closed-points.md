# Delivery report

1. Files written:
   - `dag/nodes/sec-picard-framework/lem-sc-positive-dimensional-locally-algebraic-closed-points.json` (statement, split).
   - `dag/nodes/sec-picard-framework/lem-sc-fg-domain-positive-dimension-infinite-maximals.json` (statement-only, no Mathlib match).
   - `dag/nodes/sec-picard-framework/lem-sc-affine-maximal-points-closed-in-lft-scheme.json` (statement-only, no Mathlib match).
   - `citations.json` (verbatim step citations).
2. Attachments: none. No sorry-free slopmaster2 declaration states the item or either new node.
3. WANTED: none; the cited Stacks source texts are represented by the existing literature references.
4. No source statement was changed. The imported item had no proof, so I supplied the affine reduction, the positive-dimensional finite-type domain fact, and the Jacobson closed-point transfer as separate steps. The affine reduction was corrected during review of my own draft: an affine open of the closed subset need not be an affine open of the ambient scheme, so the final proof chooses an affine open of $X$, intersects it with $Z$, and lifts maximal ideals through the quotient.
5. Nothing remains unfinished in the split. The two new facts are intentionally statement-only nodes for later stages.

## Review by M1

I read the item's source references, Varieties Tags 0478 and 0A21, and the affine argument in Algebra (the finite-type Jacobson result is Tag 00G1). I also read the existing node `lem-sc-dimension-locally-algebraic`; its statement explicitly gives the dimension of every nonempty open of an irreducible locally finite-type scheme, which is the fact used in step 1. The step also cites the existing definition nodes for finite type, irreducibility, affine schemes, closed immersions, and topological Krull dimension. I checked the hypotheses: $Z$ is irreducible and locally finite type, and an affine open $U$ of $X$ meeting $Z$ gives the affine closed intersection $V=U\cap Z$; the dimension node supplies its positive dimension.

Step 2 cites `lem-sc-fg-domain-positive-dimension-infinite-maximals`; its statement says exactly that a finitely generated field-algebra domain of positive Krull dimension has infinitely many maximal ideals. The remaining identification of maximal ideals with affine closed points is the affine-spectrum definition. Step 3 cites `lem-sc-affine-maximal-points-closed-in-lft-scheme`; its statement says exactly that a closed point of an affine open of a locally finite-type scheme is closed in the ambient scheme. Distinct maximal ideals remain distinct after inverse image in the quotient, so the conclusion is elementary from those statements.

Before creating either node I searched the whole DAG and blueprint for the affine infinitude and ambient Jacobson assertions, and searched the Lean source and Mathlib by natural-language search, semantic search, and source grep. No existing node or Mathlib declaration stated either result. I tested the new ring statement on $k[t]$ (positive dimension and infinitely many maximal ideals) and on a field (dimension zero, so the hypothesis correctly fails); the scheme statement on $\operatorname{Spec}k$ and on $\mathbb A^1_k$ with principal affine opens. The final proof avoids the false identification of an affine open of $Z$ with an affine open of $X$.
