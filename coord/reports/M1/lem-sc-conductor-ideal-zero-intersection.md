# Delivery report

Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-conductor-ideal-zero-intersection.json`: item split into three proof steps; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-reduced-ideals-zero-intersection.json`: new unsplit statement node; no Mathlib match after LeanSearch, LeanFinder, and source grep.

Attachments: none.  WANTED: none; the relevant source is available as `c1-stacks-review/varieties.tex` (Remark 09NW and Lemma 09NX).

The original item had no proof.  I retained its statement and filled its blueprint and split metadata.  The only new mathematical dependency is the reduced-ring conductor calculation, which was searched across the DAG and blueprint before being stated as a separate unsplit node.  The affine-local step uses the closed-immersion ideal description and reduced-scheme definition; the sheaf step uses the ideal-sheaf kernel description; the tensor step uses the definitions of invertibility and sheaf tensor product.  Small cases checked were $r=1$ (where $\mathcal I=\mathcal O_Y$ and restriction is the identity), $A=k[x,y]/(xy)$ with $I=(x)$ and $J_1=(y)$ (intersection $(xy)=0$), and disjoint components (extension by zero).

## Review by M1

I read Varieties Remark 09NW and the displayed equality in Lemma 09NX in `/home/ubuntu/c1-stacks-review/varieties.tex`.  The item statement matches the source's reduced component cover, conductor ideal, invertible tensor power, and restriction-on-sections assertion.  For Step 1 I checked that `def-pc-reduced-scheme` supplies reduced affine rings, `def-weil-closed-immersion` supplies affine quotient ideals, and `def-sbc-closed-immersion-ideal-sheaf` identifies those ideals with ideal-sheaf sections; these are exactly the hypotheses needed to obtain $V(I)\\cup V(J_1)=\\operatorname{Spec}(A)$.  Step 2 cites the new node, whose statement exactly gives $I\\cap J_1=0$ and the quotient isomorphism, then uses the ideal-sheaf kernel statement to pass stalkwise and on arbitrary opens.  Step 3 cites only the invertible-module and tensor-product definitions; its tensor identification is the source's projective-module clause specialized to an invertible module.  I searched the complete DAG and blueprint for the new ring statement and found no duplicate, and searched Mathlib by LeanSearch, LeanFinder, and grep with no exact theorem.  I corrected the initially unescaped TeX in both JSON files and verified the edge cases above.  `citations.json` contains a verbatim quote for every cited node in every step.
