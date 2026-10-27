# Worker report: lem-sfb-dg-cone-rotation

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-dg-cone-rotation.json`: item split into six explicit coordinate proof steps; no new subordinate nodes and no Mathlib leaf.
- `citations.json`: empty, because every proof step is a direct calculation from the item's definitions and cites no node statement.

## Attachments

None. I searched the project source for the item id, its cone and rotation terminology, and the slopmaster2 checkout for the corresponding declaration; no sorry-free project declaration states this item.

## WANTED

None. The Stacks Project source is present locally at `literature/stacks-project/dga.tex`.

## Source and statement checks

I read the item's statement and the source definitions of shifts and cones in `dga.tex`, then read Tags 09KB (`lemma-rotate-cone`), 09KC (`lemma-rotate-triangle`), 09KF (`lemma-the-same-up-to-isomorphisms`) and 09KH (`lemma-homotopy-category-pre-triangulated`). The statement's right-module convention, unchanged shifted action, cone differential, signed projection, forward rotation, and inverse rotation agree with those source conventions. I also checked the small cases $f=0$, $f=1$, the zero modules, and a DG algebra with nonzero differential: every displayed formula remains typed and the homotopies use only the module action and $f$.

## Review by N5

Step 1 checks directly that the unchanged right action on a shift satisfies the Leibniz rule and that the cone differential squares to zero; it uses only the definitions in the item, so no node citation is needed. Steps 2–4 read Tag 09KB and Tag 09KF in coordinates. For $E=C(i_f)$ I recomputed
$D(y,x,y')=(d_Yy+f(x)+y',-d_Xx,-d_Yy')$, verified that $q(y,x,y')=-x$ and $s(x)=(0,-x,f(x))$ are chain maps, and checked the explicit contraction $H(y,x,y')=(0,0,y)$ with $DH+HD=1-sq$. The identities $q i_{i_f}=-p_f$ and $(-p_{i_f})s=-f[1]$ are literal coordinate equalities. The remaining third triangle square is only homotopy-commutative, as required in $K_A$; the degree $-1$ map $J(y,x,y')=-y$ gives the exact equation.

Steps 5–6 read Tag 09KC and expand its inverse rotation without assuming a differential is $A$-linear. With $F=C(p_f[-1])$ I checked the differential
$D'(u,y,x)=(d_Xu+x,d_Yy+f(x),-d_Xx)$, the maps $r(u,y,x)=f(u)-y$ and $t(y)=(0,-y,0)$, and the contraction $H'(u,y,x)=(0,0,u)$, obtaining $D'H'+H'D'=1-tr$. The two triangle squares are $r i_g=f$ and $(-p_g)t=i_f$; the third square is homotopy-commutative via $J'(u,y,x)=(0,-u)$. Every map is $A$-linear because it is built from projections, inclusions, signs, and the $A$-linear map $f$; all homotopies have degree $-1$. No hypothesis is added, and no coefficient category is changed.

The Mathlib searches were run and retained in the item record and `searches.jsonl`: LeanFinder, LeanSearch, Loogle, and Mathlib grep. They found only ordinary cochain-complex rotation declarations, whose hypotheses do not include a general DG-algebra action or $A$-linear homotopies, so the item is not a Mathlib leaf. A whole-DAG and blueprint search found no duplicate statement. No new node was needed: all six steps are direct coordinate consequences of the definitions and the four cited Stacks source places.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.

## What was wrong or corrected

The imported item was unsplit and had inherited an unrelated null blueprint ancestor/provenance from its parent delivery. I retained that inherited null ancestor (the repository's `blueprint_refs ancestor` also returns `None`) and made the split report identify the current blueprint proof location and the immediate parent use. I corrected the proof to include the non-strict third triangle squares and their explicit homotopies; merely listing the cone maps would have omitted the sign-sensitive part of the Stacks argument.

## What remains unfinished

Nothing in this stage. The item is ready for the required dry run.
