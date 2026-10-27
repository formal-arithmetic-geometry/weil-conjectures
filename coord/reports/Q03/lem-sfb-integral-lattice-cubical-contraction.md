# Stage-1 repair: lem-sfb-integral-lattice-cubical-contraction

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-integral-lattice-cubical-contraction.json`: unchanged statement, five assembly steps totaling 1825 characters.
- `dag/nodes/sec-six-functors-basics/lem-sfb-cubical-boundary-coordinate-projections.json`: statement, unsplit, no Mathlib match. Boundary, coordinate reset maps, their product and translation/free-orbit structure.
- `dag/nodes/sec-six-functors-basics/lem-sfb-cubical-signed-coordinate-homotopy.json`: statement, unsplit, no Mathlib match. Signed paths for positive and negative endpoints and the coordinate homotopy identity.
- `citations.json`: one verbatim statement quotation for every cited node at every parent step.
- `report.md`: this repair and the full retained prior proof arguments below.
- Local evidence: `searches.jsonl`, `check_cells.py`, `repair.py`, `prior-report.md`. No Lean or compiler command was run.

Two new nodes, zero new Mathlib leaves. Both new nodes have empty proof, empty proof_deps and null proof_origin; their statements are 1931 and 1649 characters and divide the substantial computations comparably.

## Attachments

None. The item-id and cubical/contraction searches in lean/WeilConjectures found no exact completed declaration. The recorded Sheaf theorem IntegralLatticeCubical.contraction in lean/Sheaf/AlgebraicTopology/IntegralLatticeCubicalContraction.lean has `sorry` as its proof (line 158). Its docstring reproduces the same eight-step argument. Monomial Cech homotopies use a different complex. The new coordinate-reset and signed-path assertions have no exact project declaration.

## WANTED

None. The argument is agent-written; the Stacks comparison is explicitly limited and does not pretend that a missing source proves these lemmas.

## Returned point and repair

The human return requires at least two comparable statement-only nodes, all arguments retained, and a parent assembly at most 3000 characters. The sandbox initially held only dispatcher marker files, not the previously delivered JSON/report/search evidence. I copied the current live item as baseline, retained all metadata, statement, citations to definitions and historical Mathlib searches in it, and read the previous NJ report from coord/reports. A local copy is prior-report.md; its old proof argument is preserved verbatim below. This is a substantive re-split, not an unchanged re-push.

Returned steps 1, 2 and 8 are assigned to the new boundary/projections node, together with the product identification from old step 6. Returned steps 3, 4 and 5 are assigned to the new signed-coordinate-homotopy node. Neither is a restatement of the whole item: the first constructs no homotopy or exactness proof, and the second proves only the one-coordinate identity, not the total lattice contraction, translation decomposition or augmented exactness. The parent constructs h as the finite sum of preceding projections times the coordinate homotopies, telescopes, and proves kernel equals image. Thus old steps 6 and 7 remain concrete assembly, with no deleted mathematical content.

Read GOAL.md, roles/worker.md, stages/1-dag.md, SETUP.md's three levels, tools/README.md, delivery-errors B--E, the chapter and assigned unit records, and paragraph (3) of the current main-20261015 direct-image proof. The unit record is the older sec-six-functors record; the current direct-image proof is under sec-six-functors-basics. This repair stays at the same algebraic input under the inherited tame-inertia/discrete-lattice chain. It changes no unit or chapter route and no target statement. The ancestor utility returns None, as in the inherited blueprint metadata; the null from.node and via chain are retained, and each new node prepends the item to its via list.

## Mathlib and duplicate searches

Ran the required msearch.py command for both new nodes: six searches each, including LeanFinder, Loogle, LeanSearch and grep plus second phrasings. Every query/result in the JSON comes directly from searches.jsonl. All services responded; no outage is called an absence. Read the hit descriptions. Inspected DoldKan/Homotopies.lean and HomotopyEquivalence.lean: their Hσ, projections and homotopies refer to simplicial degeneracies and normalized Moore complexes. Inspected Algebra/Homology/Homotopy.lean: Homotopy, refl and constructors require homotopy data or supply the zero homotopy of equal maps. Inspected RepresentationTheory/Homological/Resolution.lean:180 and GroupHomology/Basic.lean:127: the standard/bar differential uses tuples of group elements, not lattice cells and coordinate subsets. A comparison with these complexes is not a one-line specialization. Abstract chain-map constructors likewise assume the commuting squares that the new lemma must prove. The two new lemmas therefore remain unsplit, with no Mathlib match. Historical item searches and the previous report assessment are retained, not re-invented.

Searched all dag/nodes for cubical, coordinate reset, signed coordinate, rho_i and Tags 0623/062F, and searched blueprint_refs.py for cubical, cubical lattice, coordinate reset and signed coordinate. No equivalent imported blueprint node was found. The existing cubical diagonal is a tensor diagonal and depends on this item; the lattice Koszul resolution and its triangulated cup comparison are downstream derived-invariant comparisons. None is used backwards. Same-tag comparisons are enumerated below.

## Review by Q03

I read more-algebra.tex at Tag 0623, label definition-koszul-complex, including the preceding alternating differential, and Tag 062F, label lemma-regular-koszul-regular, including its proof. The tags were checked against tags/tags. These give the Koszul notation and regular-sequence acyclicity, respectively; they do not prove a coordinate contraction. Both new nodes honestly label their explicit coordinate formulas as agent-written extractions of the returned proof, with Tag 0623 only for comparison. I also read the entire recorded Sheaf module; its theorem is sorried, so it cannot close this item.

For the boundary/projections node, I checked that the statement introduces r, all lattice bases, all integer degrees, the sign count, boundary, projections, augmentation and translation. It carries the exact d² cancellation and the p_i chain-map and commutation assertions used by parent steps 1 and 3. Its product is explicitly sε in degree zero and zero elsewhere, rather than an unidentified projection. Its final isomorphism specifies the image of every basis vector and intertwines translation; parent step 1 consequently uses the actual claimed finite free-orbit structure. No regularity, flatness or equivariance of a contraction is assumed. Empty coordinate sets and the singleton rank-zero lattice are included.

For the signed-path node, I checked that its independently introduced C, d and p formulas agree literally with those of the first node and parent. Its finite signed sum is defined for every integer endpoint and every abelian-group family, with both telescoping identities stated. The H_i formula has the insertion sign determined before insertion and explicitly vanishes when i is present. Its homotopy identity covers both basis cases and top degree. This preserves all three returned steps, including negative endpoint checks; it is not an appeal to an unspecified standard contraction.

Parent step 1 uses the boundary/projections statement for exactly the chain identities, projection maps/product and translation decomposition it states. Step 2 uses the signed-path statement for actual homomorphisms and their identity; all r summands and degrees of h are displayed. Step 3 uses those two statements to move d through P and replace dH+Hd by 1-p. The remaining finite sum of differences telescopes explicitly. The product identification is provided by the first statement; evaluating εs at 1 is elementary. Step 4 uses the previously established contraction, not a theorem hidden in a definition: it explicitly exhibits h(x) as a preimage for every cycle and every augmentation-kernel element. Its sole external citation, def-weil-pbc-module-chain-complex-homology, defines homology as kernel modulo image. I opened it and def-weil-pbc-free-module and read their statements; only the former is now a parent proof dependency. Step 5 uses the first new statement's rank-zero identification and the empty sum; the non-equivariance example is direct. All quoted statements in citations.json were verified as literal substrings, with one entry per step/node pair.

I checked the face signs again: for i<j the two removal exponents are q_i+q_j-1 and q_j+q_i. In the absent-i homotopy case, j<i gives exponents q_i+q_j and q_j+q_i-1, and j>i gives q_i+q_j+1 and q_j+q_i. In the present-i case the two i-signs multiply to +1 and the path endpoints differ by one. The endpoint formulas hold at -1 and 0 and for all negative n. These arguments are preserved verbatim in the retained-material section, not blurred into a claim of obviousness.

Small-case verification uses only Python sparse integer chains, no Lean or build tools: all 1111 cells in ranks 0..3 with coordinates -2..2 were checked for d²=0, p_i commuting with d and each other, dH_i+H_i d=1-p_i, P_r=e and dh+hd=1-e. Rank zero, no directions, all directions, mixed lower/higher indices, and negative endpoints are covered. The report records this as a finite sanity check, not a replacement for the general arguments.

B--E checks: both new nodes are statement-only and self-contained; neither cites its parent, so the new dependency edges are acyclic. Their notions are defined inline or cite the existing free-module/complex definitions. TeX is single escaped after JSON decoding. No source is attributed beyond what it says, no SGA is used, and every non-elementary parent claim cites a statement that contains it. Parent steps are all below 2000 characters; the entire parent proof is below 3000. I corrected the returned granularity by extracting the coordinate calculations, rather than merely shortening their prose. The old NJ report's conclusion that extraction was unnecessary is superseded by the explicit human re-split decision.

## Unfinished work

No mathematical issue remains in this assembly. The two new statements intentionally remain unsplit for separate workers. The first required dry run exited successfully: OK (not pushed), preflight passed, commit 1729910bba3. After correcting a report line number and making the projection quotations specific to their assembly steps, a final dry run is run before pushing.

## Retained prior arguments and ownership map

The following is the full old proof, verbatim from the current repository baseline. It is supporting material in this report, not proof steps on either statement-only node. Old steps 1/2/8 and the product identification in 6 belong to the boundary/projections child; old steps 3/4/5 belong to the signed-coordinate child. Old 6/7 are the short parent assembly and exactness argument. This preserves every cancellation and endpoint argument for the workers who will split the new nodes.

### Returned step 1

By the basis description in [def-weil-pbc-free-module], a prescribed finite integral combination for each $[v,I]$ extends uniquely to a homomorphism. Use this throughout. Put $\partial_0=0$. For distinct $i,j\in I$, removing $i$ then $j$ and removing $j$ then $i$ produce opposite signs: if $i<j$, their exponents are $q_i+q_j-1$ and $q_j+q_i$, where $q_k=\#\{l\in I:l<k\}$. Their four translated terms agree because translations in distinct coordinates commute. Pairing these terms gives $\partial^2=0$; degrees with fewer than two coordinates give zero directly. Also $\epsilon\partial_1[v,\{i\}]=1-1=0$. Thus these maps form the chain complex of [def-weil-pbc-module-chain-complex-homology] with the stated augmentation.

### Returned step 2

For $1\leq i\leq r$ let $\rho_i(v)=v-v_i u_i$, and define a degree-preserving homomorphism $p_i$ by $p_i[v,I]=0$ if $i\in I$, and $p_i[v,I]=[\rho_i(v),I]$ otherwise. If $i\notin I$, each face removes $j\ne i$ and $\rho_i(v+u_j)=\rho_i(v)+u_j$, so $p_i\partial=\partial p_i$. If $i\in I$, every face except the $i$-face is killed by $p_i$, while the two vertices of the $i$-face acquire the same $i$-coordinate zero and cancel. Hence $p_i$ is a chain map. The $p_i$ commute: each either kills a cell containing its coordinate, or resets that coordinate, independently of all others.

### Returned step 3

For any integer-indexed family $b(k)$ in an abelian group write $\Sigma_n b=\sum_{k=0}^{n-1}b(k)$ for $n>0$, $\Sigma_0 b=0$, and $\Sigma_n b=-\sum_{k=n}^{-1}b(k)$ for $n<0$. Cancelling consecutive terms gives, for every integer $n$, $\Sigma_n(b(k+1)-b(k))=b(n)-b(0)$ and $\Sigma_{n+1}b-\Sigma_n b=b(n)$; these formulas include $n=-1,0$. For $i\notin I$ define the degree-one homomorphism $$H_i[v,I]=(-1)^{q_i}\Sigma_{v_i}\bigl[\rho_i(v)+ku_i,I\cup\{i\}\bigr],\qquad q_i=\#\{j\in I:j<i\},$$ and set $H_i[v,I]=0$ for $i\in I$. Every sum is finite, so this is a well-defined homomorphism by [def-weil-pbc-free-module]. It vanishes on $C_r$ and on degrees outside the stated range.

### Returned step 4

Suppose $i\notin I$. In $\partial H_i[v,I]$, the $i$-face has sign $(-1)^{q_i}$ as well as the prefactor $(-1)^{q_i}$. Its signed sum therefore telescopes to $[v,I]-[\rho_i(v),I]$. For $j\in I$, the other face terms cancel those of $H_i\partial[v,I]$, with identical bases and summation ranges. Indeed if $j<i$, their exponents are $q_i+q_j$ and $q_j+q_i-1$; if $j>i$, they are $q_i+q_j+1$ and $q_j+q_i$. Shifting in the $j$-direction leaves $v_i$ unchanged, so this compares the actual summands also for negative $v_i$. Thus $(\partial H_i+H_i\partial)[v,I]=(1-p_i)[v,I]$ when $i\notin I$.

### Returned step 5

Suppose $i\in I$. Here $H_i[v,I]=0$. In $H_i\partial[v,I]$ all faces except the $i$-face still contain $i$ and give zero. For that face the boundary and insertion signs are both $(-1)^{q_i}$, so their product is $1$. The two path sums have the same base $\rho_i(v)$ and upper endpoints $v_i+1$ and $v_i$. Their difference is exactly $[v,I]$ by $\Sigma_{v_i+1}-\Sigma_{v_i}$. Since $p_i[v,I]=0$, this proves $\partial H_i+H_i\partial=1-p_i$ on the remaining basis elements. Linearity gives this identity in every degree, including the top degree.

### Returned step 6

Put $P_0=1$ and $P_i=p_1\cdots p_i$, and in each degree set $h=\sum_{i=1}^r P_{i-1}H_i$. Every $P_i$ is a chain map by step 2, so the identities of steps 4 and 5 yield $$\partial h+h\partial=\sum_{i=1}^r P_{i-1}(1-p_i)=\sum_{i=1}^r(P_{i-1}-P_i)=1-P_r.$$ For $I\ne\varnothing$ one factor $p_i$ kills $[v,I]$, hence $P_r=0$ in positive degree; in degree zero it resets all coordinates and sends $[v,\varnothing]$ to $[0,\varnothing]$. Thus $P_r=e$ and the required contraction identity holds, with the degree-minus-one term zero. Directly $\epsilon s(1)=1$.

### Returned step 7

For $a>0$ and $x\in C_a$ with $\partial_a x=0$, the contraction gives $x=\partial_{a+1}h_a x$, proving exactness in positive degree. If $x\in C_0$ and $\epsilon x=0$, it gives $x=\partial_1 h_0x$; the opposite inclusion follows from $\epsilon\partial_1=0$. Surjectivity at $\mathbf Z$ follows from $\epsilon s=1$. These are precisely kernel equals image at every position of the augmented complex, or vanishing homology by [def-weil-pbc-module-chain-complex-homology]. For $r=0$ there is just the basis vector $[0,\varnothing]$; identify its group with $\mathbf Z$. The empty sum gives $h=0$ and the augmentation and section are identities.

### Returned step 8

For $w\in D$, replacing $v$ by $v+w$ in each summand of $\partial[v,I]$ gives exactly $w\partial[v,I]$; also $\epsilon[v+w,\varnothing]=1=\epsilon[v,\varnothing]$. Fixing $I$ of size $a$, the subgroup with basis $[v,I]$ is the free abelian group on $D$ with its translation action, i.e. the free integral $D$-module on one orbit. The basis partitions by $I$, so $C_a$ is the direct sum of these subgroups by [def-weil-pbc-free-module]. There are finitely many such subsets of the finite set $\{1,\ldots,r\}$. No equivariance of $h$ or $s$ was used or claimed: for $r=1$, $s(1)=[0,\varnothing]$ already fails to be fixed by translation by $u_1$.

## Not duplicates

lem-sfb-cubical-boundary-coordinate-projections vs lem-sbc-connected-rational-point-geometrically-connected: the existing statement concerns A connected scheme with a rational point is geometrically connected, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs lem-sbc-section-component-noetherian-model: the existing statement concerns Local noetherian model for a section component, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs lem-sbc-section-component-cartesian: the existing statement concerns Section-component loci in a cartesian square, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs lem-sbc-affine-section-noetherian-descent: the existing statement concerns Affine noetherian descent with a compatible section, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs lem-coef-cocartesian-relative-cylinder-extension: the existing statement concerns Pointwise colimits extend a lift across its relative mapping cylinder, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs lem-zl-geometric-irreducibility-affine-local: the existing statement concerns Affine-local criterion for geometric irreducibility on an irreducible scheme, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs lem-trf-blowup-chart-regular-sequence-presentation: the existing statement concerns Affine blowup chart presentation for a regular sequence, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs lem-trf-nodal-divisorial-chart: the existing statement concerns Fine saturated nodal pushout monoid and its monoid-algebra model, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs lem-trf-koszul-derived-quotient: the existing statement concerns Koszul-regular quotient as a derived tensor product, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs lem-sc-koszul-self-ext-dual-exterior-conormal: the existing statement concerns Koszul self Ext is the dual of the exterior conormal, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs new-d3-koszul-normalized-projective-resolution: the existing statement concerns The Koszul projective resolution with its quotient augmentation, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs new-j3-koszul-projective-resolution: the existing statement concerns The Koszul chain complex is a projective resolution of its quotient, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs new-d3-koszul-quotient-tensor-homology-basis: the existing statement concerns Exterior basis of quotient-coefficient Koszul homology, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs new-e1-koszul-conormal-cycle-presentation: the existing statement concerns Koszul wedge cycles present the exterior conormal, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs lem-sfb-discrete-lattice-koszul-resolution: the existing statement concerns Discrete lattice derived invariants via a sheaf-module Koszul resolution, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs lem-sfb-integral-lattice-cubical-contraction: the parent additionally constructs the total homotopy and proves augmented exactness; this child supplies a strict coordinate-calculation ingredient, as required by the human re-split.

lem-sfb-cubical-boundary-coordinate-projections vs lem-sfb-constant-scalar-restriction-tensor: the existing statement concerns Constant scalar restriction preserves tensor, total complexes and K-flat localization, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs lem-weil-pbc-ideal-powers-local-coefficient-span: the existing statement concerns Local base-ideal coefficient span for ideal-power sections, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs lem-weil-pbc-etale-limit-binary-zero-restriction-row: the existing statement concerns Degree-zero restriction row with a certified product comparison, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs lem-weil-pbc-koszul-tensor-zeroth-boundary-saturation: the existing statement concerns Degree-zero Koszul boundaries are saturated under a quotient-regular scalar, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs def-weil-pbc-koszul-complex: this existing node defines a Koszul complex, not the stated lattice coordinate maps or their verified identities.

lem-sfb-cubical-boundary-coordinate-projections vs lem-weil-pbc-formal-kernel-polynomial-action: the existing statement concerns Finite polynomial algebra action on successive coherent formal kernels, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs lem-weil-pbc-etale-limit-binary-geometric-ladder: the existing statement concerns Restricted stage Mayer--Vietoris diagrams before colimit exactness and continuity, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs lem-weil-pbc-ideal-powers-local-coefficient-span-affine-core: the existing statement concerns Affine ideal-power coefficient span, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs lem-weil-pbc-etale-limit-binary-successor-cocone-segment: the existing statement concerns Positive-degree natural Mayer--Vietoris segment with stage-leg squares, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs lem-weil-pbc-exterior-power-free-basis: the existing statement concerns Basis of the exterior powers of a finite free module, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs lem-weil-pbc-regular-quotient-ideal-intersection: the existing statement concerns Intersection with an ideal generated by a regular sequence modulo another ideal, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs lem-weil-pbc-formal-associated-graded-polynomial-cover: the existing statement concerns Polynomial evaluation locally spans the associated graded extended ideal algebra, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-boundary-coordinate-projections vs lem-exc-dimension-formula-universally-catenary-finite-type-domain: the existing statement concerns Dimension formula for finite type extensions of universally catenary domains, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-sbc-connected-rational-point-geometrically-connected: the existing statement concerns A connected scheme with a rational point is geometrically connected, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-sbc-section-component-noetherian-model: the existing statement concerns Local noetherian model for a section component, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-sbc-section-component-cartesian: the existing statement concerns Section-component loci in a cartesian square, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-sbc-affine-section-noetherian-descent: the existing statement concerns Affine noetherian descent with a compatible section, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-coef-cocartesian-relative-cylinder-extension: the existing statement concerns Pointwise colimits extend a lift across its relative mapping cylinder, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-zl-geometric-irreducibility-affine-local: the existing statement concerns Affine-local criterion for geometric irreducibility on an irreducible scheme, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-trf-blowup-chart-regular-sequence-presentation: the existing statement concerns Affine blowup chart presentation for a regular sequence, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-trf-nodal-divisorial-chart: the existing statement concerns Fine saturated nodal pushout monoid and its monoid-algebra model, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-trf-koszul-derived-quotient: the existing statement concerns Koszul-regular quotient as a derived tensor product, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-sc-koszul-self-ext-dual-exterior-conormal: the existing statement concerns Koszul self Ext is the dual of the exterior conormal, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs new-d3-koszul-normalized-projective-resolution: the existing statement concerns The Koszul projective resolution with its quotient augmentation, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs new-j3-koszul-projective-resolution: the existing statement concerns The Koszul chain complex is a projective resolution of its quotient, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs new-d3-koszul-quotient-tensor-homology-basis: the existing statement concerns Exterior basis of quotient-coefficient Koszul homology, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs new-e1-koszul-conormal-cycle-presentation: the existing statement concerns Koszul wedge cycles present the exterior conormal, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-sfb-discrete-lattice-koszul-resolution: the existing statement concerns Discrete lattice derived invariants via a sheaf-module Koszul resolution, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-sfb-integral-lattice-cubical-contraction: the parent additionally constructs the total homotopy and proves augmented exactness; this child supplies a strict coordinate-calculation ingredient, as required by the human re-split.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-sfb-constant-scalar-restriction-tensor: the existing statement concerns Constant scalar restriction preserves tensor, total complexes and K-flat localization, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-weil-pbc-ideal-powers-local-coefficient-span: the existing statement concerns Local base-ideal coefficient span for ideal-power sections, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-weil-pbc-etale-limit-binary-zero-restriction-row: the existing statement concerns Degree-zero restriction row with a certified product comparison, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-weil-pbc-koszul-tensor-zeroth-boundary-saturation: the existing statement concerns Degree-zero Koszul boundaries are saturated under a quotient-regular scalar, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs def-weil-pbc-koszul-complex: this existing node defines a Koszul complex, not the stated lattice coordinate maps or their verified identities.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-weil-pbc-formal-kernel-polynomial-action: the existing statement concerns Finite polynomial algebra action on successive coherent formal kernels, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-weil-pbc-etale-limit-binary-geometric-ladder: the existing statement concerns Restricted stage Mayer--Vietoris diagrams before colimit exactness and continuity, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-weil-pbc-ideal-powers-local-coefficient-span-affine-core: the existing statement concerns Affine ideal-power coefficient span, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-weil-pbc-etale-limit-binary-successor-cocone-segment: the existing statement concerns Positive-degree natural Mayer--Vietoris segment with stage-leg squares, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-weil-pbc-exterior-power-free-basis: the existing statement concerns Basis of the exterior powers of a finite free module, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-weil-pbc-regular-quotient-ideal-intersection: the existing statement concerns Intersection with an ideal generated by a regular sequence modulo another ideal, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-weil-pbc-formal-associated-graded-polynomial-cover: the existing statement concerns Polynomial evaluation locally spans the associated graded extended ideal algebra, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

lem-sfb-cubical-signed-coordinate-homotopy vs lem-exc-dimension-formula-universally-catenary-finite-type-domain: the existing statement concerns Dimension formula for finite type extensions of universally catenary domains, not the explicit cubical coordinate maps and identities stated here; a common Koszul comparison tag does not identify these statements.

