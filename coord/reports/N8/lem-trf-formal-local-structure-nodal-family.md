# N8 stage-1 repair: lem-trf-formal-local-structure-nodal-family

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-formal-local-structure-nodal-family.json`: same statement; five-step assembly, 1892 characters.
- `dag/nodes/sec-trace-formula/lem-trf-nodal-stalk-completion-reduction.json`: statement; status `unsplit`; no Mathlib match, no proof steps or proof dependencies.
- `dag/nodes/sec-trace-formula/lem-trf-split-node-coordinate-lifting.json`: statement; status `unsplit`; no Mathlib match, no proof steps or proof dependencies.
- `dag/nodes/sec-trace-formula/lem-trf-nodal-substitution-closed-fibre.json`: statement; status `unsplit`; no Mathlib match, no proof steps or proof dependencies.
- `dag/nodes/sec-trace-formula/lem-trf-complete-flat-fibre-isomorphism.json`: statement; status `unsplit`; no Mathlib match, no proof steps or proof dependencies.
- `dag/nodes/sec-trace-formula/lem-trf-nodal-polynomial-model-completion.json`: statement; status `unsplit`; no Mathlib match, no proof steps or proof dependencies.

`citations.json` contains one exact conclusion-bearing statement quotation per assembly step. Search commands and their actual answers remain in `searches.jsonl` and `search-results/`; the pre-existing item Mathlib searches are retained unchanged. Auxiliary files remain sandbox-only.

## Attachments

None. Searched `lean/WeilConjectures/` by the item id and the formal-local/nodal-family concepts: no project declaration states the item. The corresponding library declaration `AlgebraicGeometry.formalLocalStructureNodalFamily` in `lean/Sheaf/TraceFormula/FormalLocalStructureNodalFamily.lean:316` has a whole-proof `sorry`, so it is not an attachment. No Lean was edited or compiled.

## WANTED

None. The Stacks sources needed for this split and its proof handoffs are available locally.

## What was wrong and what was repaired

The human returned the 14-step proof for re-splitting: its 9747 characters described too much work for one worker. I extracted five independently stated lemmas of comparable argument size, all status `unsplit`. The parent statement, source, statement dependencies, blueprint fields, pointers and maintainer metadata remain unchanged. I did not just shorten the proof: every original step is assigned below to one new node, and its complete text, citations and source are retained verbatim in this report. No new node classifies the whole family. In particular the coordinate-lifting node only produces elements and convergent sequences, the substitution node only constructs a map, and the algebra criterion only proves a given map is invertible. The last node concerns a fixed polynomial model, not any given family.

The original source prints $x\mapsto\bar v$ in its second coordinate; I read this as $y\mapsto\bar v$, as the old proof already does. This is a source display typo, not a change of the item statement. No STATEMENT-DISPUTED correction is needed.

## What remains

The five new nodes deliberately carry no proofs: their proofs are separate future stage-1 work, with the full old arguments below as handoff material. There is no unfinished part of this assembly or of this repair beyond the required delivery checks.

## Review by N8

I read `curves.tex` Tag 0CBX (`lemma-formal-local-structure-nodal-family`) in full, including its coordinate correction and limit proof, and Tag 0CBY (`lemma-etale-local-structure-nodal-family`), the third paragraph of its first proof identifying the polynomial model. I read the current main-20261015 chapter, unit and ancestor texts and the recorded unit/chapter: the nodal chain is a historical local-equation input, not a replacement of the current contracting-correspondence route. No unit or chapter realization is changed, and no SGA route is used. I checked delivery-errors B through E, including the merged copy of those sections.

For the first new node I checked the first paragraph of 0CBX and `more-algebra.tex` Tag 0C4G (`lemma-flat-completion`), and read every localization, Noetherianity, completion and fibre-quotient statement cited by original steps 1–3. Only the base stalk is assumed Noetherian: localizing a finite type algebra over that stalk proves the target stalk Noetherian; no neighbourhood-wide Noetherian hypothesis is inserted. Maximal ideals and residue fields are the canonical ones. The completed map sends the generators of the extended base maximal ideal into the extended target maximal ideal, so it is local. The fibre comparison is an algebra comparison with its actual quotient map, not merely a ring isomorphism.

For the second new node I checked the second and third paragraphs of 0CBX and the complete-local quotient statement (`algebra.tex` Tag 0325, `lemma-quotient-complete-local`). Its statement gives sequences with an arbitrary starting pair of lifts, consecutive-error estimates, convergence and the exact relation; its proof is not hidden inside the statement. The original correction formula needs $r\ge1$ for $2r\ge r+1$. The Noetherian complete quotient makes $\mathfrak mB$ closed in the $\mathfrak n$-adic topology. Thus the limiting coordinates retain their reductions without requiring $\mathfrak mB$-adic completeness. No flatness, characteristic restriction or coefficient-field section is used.

For the third new node I checked the third/final paragraphs of 0CBX and opened the statements for power-series Noetherianity, locality, combined-ideal completeness, complete local quotients, adic evaluation and coefficient-reduction kernel. A finitely generated base maximal ideal is available by Noetherianity. The quotient equation is in the displayed maximal ideal because $h\in\mathfrak m$. Its statement includes the actual substitution formula and equality of the induced closed-fibre map to the chosen $\theta$, so the assembly does not assume that specifying generators determines arbitrary maps on infinite series. That equality is justified in the original argument by matching every finite truncation and using separatedness.

For the fourth new node I read the last paragraph of 0CBX, `algebra.tex` Tags 00ME (`lemma-mod-injective`) and 0394 (`lemma-finite-after-completion`), and the existing Nakayama statement. This is a criterion for a supplied morphism, not existence of a nodal presentation. With $R=A,S=N=C,M=B$, injectivity modulo $\mathfrak m$ invokes 00ME without assuming $C$ flat over $A$. The closed-fibre isomorphism identifies the maximal ideals of those quotient local rings: taking inverse images and using $\mathfrak mB\subseteq\mathfrak cB$ gives $\mathfrak n=\mathfrak cB$, and identifies residue fields. Both maximal ideals are finitely generated. Thus 0394 gives finiteness over the already complete $C$ with its actual action via $\phi$; Nakayama with the element $1$ gives surjectivity. In the nodal application this ideal comparison is exactly the old step 11 calculation $\mathfrak n=\mathfrak mB+(u,v)B$. The statement does not assume that $B$ is finite in advance.

For the fifth new node I checked the stated paragraph of 0CBY and opened the combined-ideal coefficient criterion, completeness-over-complete-base, affine-stalk, Noetherian permanence and completion-of-quotient statements. This node includes the finite-level comparisons and their compatibility, the localization/quotient identification and the residue field. Completion here uses $(\mathfrak m,x,y)$, not just $(x,y)$. Denominators outside that maximal ideal are units modulo each power; the explicit inverse and coefficient tests are preserved in old steps 13–14 below. The comparison preserves coefficients and variables, so the equation $xy-h$ is sent to that same equation.

Every assembly citation was re-read from its statement after writing it. Step 1 uses the completed-stalk node to obtain exactly Noetherianity, completeness, the flat local coefficient map and the fibre isomorphism; composing with the hypothesis supplies $\theta$. Step 2 uses the lifting node only for $h,u,v$ and their reductions and relation, all explicitly supplied in that statement. Step 3 uses the substitution node for a local map from a complete Noetherian source and its closed-fibre isomorphism. Step 4 checks the criterion's hypotheses using steps 1 and 3 and takes the inverse of its conclusion. Step 5 uses the polynomial node for the specified point, its residue field and the completed model, composing isomorphisms from step 4 and the residue-field comparison of step 1. These are five non-elementary applications followed only by elementary composition/inversion; no additional comparison is left uncited. The exact statement of each cited node is copied in `citations.json`. Each proof step has fewer than 2000 characters.

I tested the new statements on $A=k$, on $A=k[[t]]$ with $B=k[[t,x,y]]/(xy-t)$, and on $A=k[\epsilon]/(\epsilon^2)$ with $h=0$ or $h=\epsilon$. Over a field the lifting sequences may be constant; over a nilpotent base the errors eventually vanish; no division by 2 occurs, so characteristic 2 works. The isomorphism criterion also works with $C=B$ and an arbitrary non-Noetherian local base because its proof only needs Noetherianity of $C,B$; the flatness assumption excludes the false quotient-map example $A=C=k[[t]]$, $B=k$. Mixed characteristic is allowed: the coefficient map is always $A\to B$, with no chosen section of $k$ into $A$. The model-origin ideal is proper since its quotient is the nonzero residue field $k$, including $h=0$ and nilpotent $h$.

Mathlib searches used msearch.py for every new id, with LeanFinder, Loogle and source grep plus LeanSearch and a second semantic phrasing. Actual output is recorded, including the LeanSearch rate-limit failures. I inspected the local definitions `AdicCompletion.flat_of_isNoetherian` at AsTensorProduct.lean:379, `IsLocalRing.linearCombination_bijective_of_flat` at LocalRing/Module.lean:294, `MvPowerSeries.toAdicCompletionAlgEquiv` at MvPowerSeries/Equiv.lean:344, and the hypotheses of Evaluation.lean. The remote Loogle query `MvPowerSeries, Ideal.Quotient` returned an unknown identifier, so I ran `MvPowerSeries, RingHom.ker` and a focused grep as repairs. Its remote `ker_map_of_fg` hit is unavailable in the pinned local Mathlib source, and in any event is only a coefficient-kernel component already represented by the existing kernel node. None of these candidates is a one-line specialization of a new statement.

DAG and blueprint searches were made by Stacks tags and by nodal family, complete local, completion, power series, closed fibre, coordinate and flat local concepts; I also read the relevant existing completion/polynomial and node-normal-form statements. The differences are listed below. New nodes are self-contained, definition references name the actual notions, have no proof steps, no proof dependencies and no proof origin, and are not Mathlib leaves. The current item statement is byte-identical to the returned version.

## Argument distribution

| New node | Original steps | Original argument characters |
| --- | --- | ---: |
| lem-trf-nodal-stalk-completion-reduction | 1, 2, 3 | 1844 |
| lem-trf-split-node-coordinate-lifting | 4, 5, 6 | 2231 |
| lem-trf-nodal-substitution-closed-fibre | 7, 8, 9 | 2136 |
| lem-trf-complete-flat-fibre-isomorphism | 10, 11, 12 | 1573 |
| lem-trf-nodal-polynomial-model-completion | 13, 14 | 1963 |

The following is the full returned proof, divided by the five interfaces. It is handoff material for future workers, not proof steps in the new unsplit JSON nodes.

### lem-trf-nodal-stalk-completion-reduction

Original step 1:

Put $A_0=\mathcal O_{S,s}$ and $B_0=\mathcal O_{T,t}$. The local map $A_0\to B_0$ is flat by the definition of flatness at $t$. To check Noetherianity of $B_0$ without assuming $S$ locally Noetherian, choose affine neighbourhoods $\operatorname{Spec}R_0$ of $s$ and $\operatorname{Spec}D$ of $t$ with $D$ finite type over $R_0$. The affine-stalk localization identifications give $A_0=(R_0)_{\mathfrak p}$ and $B_0=D_{\mathfrak q}$, with $\mathfrak q\cap R_0=\mathfrak p$. Inverting $R_0\setminus\mathfrak p$ first does not change $D_{\mathfrak q}$: each such denominator is already a unit there. Thus $B_0$ is a localization of the finite type $A_0$-algebra $D\otimes_{R_0}A_0$. This algebra, and then its localization $B_0$, are Noetherian by the two cited permanence statements.

Uses: def-weil-flat-morphism, def-weil-finite-type-morphism, lem-weil-pbc-affine-open-stalk-localization, lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-localization-noetherian

Source: literature/stacks-project/curves.tex — Tag 0CBX, lemma-formal-local-structure-nodal-family, first paragraph; Tag 00FN, algebra-lemma-Noetherian-permanence; Tag 01HV, schemes-lemma-spec-sheaves

Original step 2:

Set $A=\widehat {A_0}$, $B=\widehat {B_0}$, $\mathfrak m=\mathfrak m_{A_0}A$, and $\mathfrak n=\mathfrak m_{B_0}B$. The completion-local-ring statement identifies these as the maximal ideals and identifies both residue fields with $k=\kappa(s)=\kappa(t)$. The completion-Noetherian statement makes $A,B$ Noetherian. Their maximal ideals are finitely generated, and the adic-completion-mod-ideal statement makes them complete for these maximal ideals. The flat-completion statement applies to the flat local map of Noetherian local rings $A_0\to B_0$, so $A\to B$ is flat.

Uses: lem-weil-pbc-local-completion-local-ring, lem-weil-pbc-adic-completion-noetherian, lem-weil-pbc-adic-completion-mod-ideal, lem-weil-pbc-flat-completion

Source: literature/stacks-project/curves.tex — Tag 0CBX, first paragraph; Tags 05GI (algebra-lemma-radical-completion), 05GG (algebra-lemma-hathat-finitely-generated), 0316 (algebra-lemma-completion-Noetherian-Noetherian), 0C4G (more-algebra-lemma-flat-completion)

Original step 3:

The fibre-stalk quotient statement gives $B_0/\mathfrak m_{A_0}B_0\cong\mathcal O_{T_s,t}$. Apply the local-completion-quotient statement to this surjection, whose source $B_0$ is Noetherian local. Its completed kernel is $\mathfrak m_{A_0}B=\mathfrak mB$, and the quotient has the induced local maximal ideal. Hence the assumed split-fibre isomorphism supplies a $k$-algebra isomorphism $B/\mathfrak mB\cong k[[x,y]]/(xy)$. Denote by $\bar u,\bar v$ the classes of $x,y$ in $B/\mathfrak mB$.

Uses: lem-sbc-scheme-fibre-stalk-quotient, lem-weil-pbc-local-completion-quotient

Source: literature/stacks-project/curves.tex — Tag 0CBX, first paragraph; Tag 0CBW, curves-lemma-split-node; local completion of a quotient via Tags 00MA (algebra-lemma-completion-tensor), 00MB (algebra-lemma-completion-flat)


### lem-trf-split-node-coordinate-lifting

Original step 4:

Choose lifts $u_1,v_1\in B$ of $\bar u,\bar v$ and put $h_1=0$. They lie in $\mathfrak n$, and $u_1v_1-h_1\in\mathfrak mB$. More generally, every $b\in B$ can be written $b=a+u_1p+v_1q+\epsilon$ with $a\in A$, $p,q\in B$, $\epsilon\in\mathfrak mB$: reduce $b$ in $k[[x,y]]/(xy)$, subtract its constant coefficient (lifted from $k$ to $A$), and factor the remaining series into $x$ times a series plus $y$ times a series. Lift these two series classes to $B$. The same decomposition works with any $u,v$ lifting $\bar u,\bar v$.

Uses: none (elementary decomposition or multiplication).

Source: literature/stacks-project/curves.tex — Tag 0CBX, first and second paragraphs: lifts and the decomposition of each coefficient b_i

Original step 5:

For the induction step suppose $n\ge1$, $h\in\mathfrak m$, and $uv-h=\delta\in\mathfrak m^nB$, with $u,v$ lifting $\bar u,\bar v$. Write a finite sum $\delta=\sum_i f_ib_i$, $f_i\in\mathfrak m^n$, and use the preceding decomposition to write $b_i=a_i+up_i+vq_i+\epsilon_i$ with $a_i\in A$, $\epsilon_i\in\mathfrak mB$. Define $u'=u-\sum_i f_iq_i$, $v'=v-\sum_i f_ip_i$, and $h'=h+\sum_i f_ia_i$. Direct multiplication gives
$$u'v'-h'=\sum_i f_i\epsilon_i+(\sum_i f_iq_i)(\sum_j f_jp_j)\in\mathfrak m^{n+1}B,$$
since $2n\ge n+1$. Also $u'-u,v'-v\in\mathfrak m^nB$, $h'-h\in\mathfrak m^n$, and $h'\in\mathfrak m$. This proves the inductive improvement and preserves the chosen reductions.

Uses: none (elementary decomposition or multiplication).

Source: literature/stacks-project/curves.tex — Tag 0CBX, second paragraph, the displayed coordinate corrections and their product

Original step 6:

Starting from $(u_1,v_1,h_1)$, repeat the preceding improvement to obtain $u_n,v_n\in B$, $h_n\in\mathfrak m$ with consecutive differences in $\mathfrak m^nB,\mathfrak m^nB,\mathfrak m^n$ respectively and $u_nv_n-h_n\in\mathfrak m^nB$. Because $\mathfrak mB\subseteq\mathfrak n$, their reductions modulo any fixed power of $\mathfrak n$ (and of $\mathfrak m$ for $h_n$) eventually stabilize. Completeness, in the inverse-limit definition, supplies $u_\infty,v_\infty\in B$, $h\in A$ with those stabilized coordinates. The identities $u_nv_n-h_n\in\mathfrak n^n$ imply $u_\infty v_\infty=h$ by separatedness. The classes $u_\infty,v_\infty$ still lift $\bar u,\bar v$: the ideal $\mathfrak mB$ is closed for the $\mathfrak n$-adic topology, since $B/\mathfrak mB$ is a complete local quotient and hence separated for its induced maximal ideal. Likewise $\mathfrak m$ is closed in $A$, so $h\in\mathfrak m$. Only maximal-ideal completeness of $B$ is needed; no assertion of $\mathfrak mB$-adic completeness is made here.

Uses: def-weil-pbc-adically-complete-ring, lem-weil-pbc-complete-local-quotient

Source: literature/stacks-project/curves.tex — Tag 0CBX, third paragraph, the induction and passage to limits; Tag 0325, algebra-lemma-quotient-complete-local


### lem-trf-nodal-substitution-closed-fibre

Original step 7:

Let $R=A[[x,y]]$ and $\mathfrak a=\mathfrak mR+(x,y)$. The power-series Noetherian and local-ring statements show that $R$ is Noetherian local with maximal ideal $\mathfrak a$: a series with zero constant term is $xF+yG$, so the constant-term description of that maximal ideal is exactly this sum. The complete-over-complete-base statement makes $R$ $\mathfrak a$-adically complete. Put $C=R/(xy-h)$. Since $h\in\mathfrak m$, the equation belongs to $\mathfrak a$; the complete-local-quotient statement shows that $C$ is Noetherian local and complete, with maximal ideal the image $\mathfrak a_C$ of $\mathfrak a$.

Uses: lem-weil-pbc-power-series-noetherian, lem-weil-pbc-power-series-local-ring, lem-weil-pbc-power-series-complete-over-complete-base, lem-weil-pbc-complete-local-quotient

Source: literature/stacks-project/curves.tex — Tag 0CBX, third paragraph, construction of the source algebra; Tags 0306 (algebra-lemma-Noetherian-power-series), 032C (algebra-remark-Noetherian-complete-local-ring-universally-catenary), 0325 (algebra-lemma-quotient-complete-local)

Original step 8:

Apply the adic-evaluation statement with coefficient map $A\to B$, ideal $\mathfrak n$, and the elements $u_\infty,v_\infty\in\mathfrak n$. It supplies an $A$-algebra homomorphism $R\to B$ sending $x,y$ to these elements. The identity $u_\infty v_\infty=h$ makes it factor through an $A$-algebra homomorphism $\phi:C\to B$. It is local: each generator of $\mathfrak a_C$, namely an element of $\mathfrak m$ or one of $x,y$, maps into $\mathfrak n$.

Uses: lem-weil-pbc-power-series-adic-evaluation

Source: literature/stacks-project/curves.tex — Tag 0CBX, third paragraph, the displayed homomorphism; universal property as used in Tag 07NL, more-algebra-lemma-power-series-ring-over-Cohen-fs

Original step 9:

The coefficient-reduction kernel statement applies to the finitely generated ideal $\mathfrak m$ of $A$ and gives kernel $\mathfrak mR$ for $R\to k[[x,y]]$. This map is surjective: choose in $A$ a lift of each coefficient of a given series. Since $h\in\mathfrak m$, it identifies $C/\mathfrak mC$ with $k[[x,y]]/(xy)$. The reduction of $\phi$ sends $x,y$ to $\bar u,\bar v$ and agrees with the chosen isomorphism of step 3. Indeed, modulo the $N$-th power of the maximal ideal of $B/\mathfrak mB$ both maps send a series to the image of its truncation below total degree $N$: for the reduction of $\phi$ by the explicit formula of the adic-evaluation statement, and for the chosen isomorphism because it is a $k$-algebra isomorphism of local rings, hence maps $(x,y)^N$ into the $N$-th power of the maximal ideal. Both send $x,y$ to $\bar u,\bar v$ and constants to constants, so the two maps agree at every finite truncation and then agree by separatedness of the complete local quotient $B/\mathfrak mB$. Thus $\bar\phi:C/\mathfrak mC\to B/\mathfrak mB$ is an isomorphism.

Uses: lem-sbc-mv-power-series-quotient-kernel, lem-weil-pbc-complete-local-quotient

Source: literature/stacks-project/curves.tex — Tag 0CBX, last paragraph: isomorphism after dividing by the base maximal ideal; coefficient reduction used in Tag 0EYB, pione-lemma-purity-smooth-over-depth2


### lem-trf-complete-flat-fibre-isomorphism

Original step 10:

Apply the flat-mod-injective statement with its $R=A$, $S=C$, $N=C$, $M=B$, and $u=\phi$. The map $A\to C$ is local, $C$ is Noetherian, $C$ is a finite module over itself, and $B$ is flat over $A$ by step 2. Step 9 supplies the required injectivity modulo $\mathfrak m$. The statement therefore implies that $\phi$ is injective. In particular this use needs no separate flatness assertion for the hypersurface $C$.

Uses: lem-weil-pbc-flat-mod-injective

Source: literature/stacks-project/curves.tex — Tag 0CBX, last sentence; Tag 00ME, algebra-lemma-mod-injective

Original step 11:

In the closed fibre $B/\mathfrak mB\cong k[[x,y]]/(xy)$ the maximal ideal is $(\bar u,\bar v)$, by the local-ring and quotient-local-structure statements. Taking its inverse image in $B$ gives $\mathfrak n=\mathfrak mB+(u_\infty,v_\infty)B=\mathfrak a_CB$. Consequently $B/\mathfrak a_CB=k$, a one-dimensional vector space over $C/\mathfrak a_C=k$. Apply the finite-after-completion statement to the local map $C\to B$. Both maximal ideals are finitely generated since these rings are Noetherian. Because both rings are already complete for their maximal ideals, its finite completed-module conclusion identifies $B$ as a finite $C$-module via $\phi$; the completed action agrees with $\phi$ on elements by its coordinatewise definition.

Uses: lem-weil-pbc-power-series-local-ring, lem-weil-pbc-quotient-local-structure, lem-weil-pbc-finite-after-completion

Source: literature/stacks-project/curves.tex — Tag 0CBX, last paragraph, surjectivity by completeness; Tag 0394, algebra-lemma-finite-after-completion, applied with source C and target B

Original step 12:

The element $1\in B$ generates $B/\mathfrak a_CB=k$. Nakayama's local-generators statement for the finite $C$-module $B$ now implies that $1$ generates $B$ over $C$. Thus $\phi$ is surjective. Together with step 10 this gives the required $A$-algebra isomorphism $B\cong A[[x,y]]/(xy-h)$. This implements the source's completeness/surjectivity argument through the existing finite-after-completion and Nakayama interfaces.

Uses: lem-weil-pbc-nakayama-local-generators

Source: literature/stacks-project/curves.tex — Tag 0CBX, final paragraph; Tag 00DV, algebra-lemma-NAK, and Tag 0394, algebra-lemma-finite-after-completion


### lem-trf-nodal-polynomial-model-completion

Original step 13:

For the equivalent polynomial-model formulation put $P=A[x,y]$, $\mathfrak q=\mathfrak mP+(x,y)$ and $D=P_{\mathfrak q}$. Here $P/\mathfrak q=k$, so $\mathfrak q$ is maximal. The map $P\to R=A[[x,y]]$ identifies $P/\mathfrak q^r$ with $R/\mathfrak a^r$ for every $r\ge1$: truncate above total degree $r-1$, and use the combined-ideal coefficient criterion to check that the kernel on polynomials consists exactly of those whose coefficient of $x^iy^j$ lies in $\mathfrak m^{r-i-j}$ whenever $i+j<r$. Such polynomials belong to $\mathfrak q^r$ term by term. Every denominator outside $\mathfrak q$ is already a unit in this quotient: it has an invertible constant coefficient in $A$, and its remaining part is nilpotent modulo $\mathfrak q^r$, so a finite geometric sum gives its inverse. Therefore $D/(\mathfrak qD)^r\cong R/\mathfrak a^r$, compatibly with the transition maps, constants and variables. Taking compatible sequences and using the completeness of $R$ gives $\widehat D\cong R$ as $A$-algebras.

Uses: lem-weil-pbc-power-series-combined-ideal-coefficients, lem-weil-pbc-power-series-complete-over-complete-base, def-weil-pbc-localization-at-prime, def-weil-pbc-adic-completion

Source: literature/stacks-project/curves.tex — Tag 0CBY, curves-lemma-etale-local-structure-nodal-family, first proof, third paragraph, the completed-model identification; coefficient calculation for Tag 032C

Original step 14:

Let $M_h=\operatorname{Spec}(P/(xy-h))$ and let $o$ be its point with ideal $\mathfrak q/(xy-h)$. Its residue field is $k$ since evaluation $x=y=0$ gives $P/(xy-h,\mathfrak m,x,y)=k$. The affine-stalk localization statement identifies $\mathcal O_{M_h,o}$ with $(P/(xy-h))_{\mathfrak q/(xy-h)}$. The fraction map identifies this ring with $D/(xy-h)D$: the denominators on both sides are exactly the images of $P\setminus\mathfrak q$, and $a/s$ is in the kernel precisely when some denominator outside $\mathfrak q$ times $a$ belongs to $(xy-h)$. The ring $D$ is Noetherian by finite-type and localization permanence over the Noetherian ring $A$. Apply local-completion-quotient to $D\to D/(xy-h)D$, and use the constant-and-variable preserving identification of step 13. It gives $\widehat{\mathcal O}_{M_h,o}\cong\widehat D/(xy-h)\widehat D\cong A[[x,y]]/(xy-h)$. Composing with step 12 proves the equivalent formulation, with its specified residue field.

Uses: lem-weil-pbc-affine-open-stalk-localization, lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-localization-noetherian, lem-weil-pbc-local-completion-quotient

Source: literature/stacks-project/curves.tex — Tag 0CBY, first proof, third paragraph; Tags 01HV (schemes-lemma-spec-sheaves), 00FN (algebra-lemma-Noetherian-permanence), 00MA (algebra-lemma-completion-tensor)


## Not duplicates

lem-trf-nodal-stalk-completion-reduction vs lem-trf-formal-local-structure-nodal-family: it proves only the completed-stalk and closed-fibre reduction for a general flat finite type morphism, with no nodal-presentation conclusion.
lem-trf-split-node-coordinate-lifting vs lem-trf-formal-local-structure-nodal-family: it is an algebraic coordinate-lifting lemma with prescribed special-fibre coordinates and controlled convergent sequences, and does not construct or prove a nodal presentation.
lem-trf-nodal-substitution-closed-fibre vs lem-trf-formal-local-structure-nodal-family: it constructs the supplied-coordinate substitution map and proves its fibre compatibility; it does not prove the map injective or surjective.
lem-trf-complete-flat-fibre-isomorphism vs lem-trf-formal-local-structure-nodal-family: it is a general criterion for an already supplied morphism C to B, with no nodal equation or family hypotheses.
lem-trf-nodal-polynomial-model-completion vs lem-trf-nodal-generic-component-closure: the existing statement concerns closure of a generic fibre component over a valuation ring and its boundary finite etale schemes; the new node only compares fixed-model polynomial, localized and formal quotient rings at their origin.
lem-trf-nodal-polynomial-model-completion vs lem-trf-valuation-smooth-branches-strict-chart: the existing statement produces strict etale charts of multipointed semistable curves over valuation rings; the new node only compares fixed-model polynomial, localized and formal quotient rings at their origin.
lem-trf-nodal-polynomial-model-completion vs lem-trf-formal-local-structure-nodal-family: it computes the completion of a fixed polynomial model over an arbitrary complete Noetherian local coefficient ring; it does not classify an arbitrary family.
lem-trf-nodal-polynomial-model-completion vs lem-trf-ordered-nodal-branch-overlap: the existing statement compares ordered branch ideals on etale overlaps over valuation rings; the new node only compares fixed-model polynomial, localized and formal quotient rings at their origin.
lem-trf-nodal-polynomial-model-completion vs lem-trf-valuation-symmetric-nodal-blowup: the existing statement computes symmetric nodal blowups and improves component smoothness over valuation rings; the new node only compares fixed-model polynomial, localized and formal quotient rings at their origin.
lem-trf-nodal-polynomial-model-completion vs lem-trf-nodal-log-regularity: the existing statement establishes log regularity of a global boundary pair; the new node only compares fixed-model polynomial, localized and formal quotient rings at their origin.
lem-trf-nodal-polynomial-model-completion vs lem-trf-nodal-etale-chart: the existing statement produces etale charts and log-monoid expressions for families over log regular bases; the new node only compares fixed-model polynomial, localized and formal quotient rings at their origin.
lem-trf-nodal-polynomial-model-completion vs lem-trf-nodal-family-etale-local-model: the existing statement constructs actual etale local charts of a family, not the completed stalk of a fixed model; the new node only compares fixed-model polynomial, localized and formal quotient rings at their origin.
lem-trf-nodal-polynomial-model-completion vs lem-sfb-nodal-branch-double-cover: the existing statement constructs a finite etale double cover parametrizing normalization branches; the new node only compares fixed-model polynomial, localized and formal quotient rings at their origin.
lem-trf-nodal-polynomial-model-completion vs lem-sfb-dvr-nodal-chart-blowup-calculus: the existing statement treats regularity and blowup charts of xy=pi^n over DVRs, with no general complete-local-base completion comparison; the new node only compares fixed-model polynomial, localized and formal quotient rings at their origin.
lem-trf-nodal-polynomial-model-completion vs lem-sfb-persistent-node-normalization: the existing statement constructs persistent-node normalization and its conductor pushout over a DVR; the new node only compares fixed-model polynomial, localized and formal quotient rings at their origin.
lem-trf-nodal-polynomial-model-completion vs def-sfb-nodal-branch-scheme: the existing statement defines a graph-cone blowup branch scheme and states no polynomial-model completion comparison; the new node only compares fixed-model polynomial, localized and formal quotient rings at their origin.

lem-trf-split-node-coordinate-lifting vs lem-trf-formal-binary-morse: the existing statement straightens one power series over a field using a nonsingular quadratic form; the new node lifts two fibre coordinates over an arbitrary complete local coefficient ring.
lem-trf-complete-flat-fibre-isomorphism vs lem-weil-pbc-flat-local-completion-iso: the existing statement assumes flatness of the very map whose completions are compared and equality of extended maximal ideals; the new criterion assumes only B flat over an auxiliary A and deduces invertibility of C to B from its A-closed-fibre map.
lem-trf-complete-flat-fibre-isomorphism vs lem-weil-pbc-complete-source-surjective-mod-ideal: the existing statement supplies surjectivity with respect to one chosen ideal; it supplies neither injectivity from A-flatness nor finiteness over C for the maximal-complete-ring setting here.
lem-trf-nodal-polynomial-model-completion vs lem-weil-pbc-polynomial-local-completion-formally-smooth: formal smoothness of a one-variable local completion does not identify a two-variable nodal hypersurface completion.
lem-trf-nodal-polynomial-model-completion vs lem-weil-pbc-polynomial-quotient-completion-fibre-iso: the existing statement compares tensor products with residue fields after coefficient quotienting; it does not identify the completed origin stalk of xy-h with a formal power-series quotient.

## Validation

Server review_split preliminary check passed before the report was written. The first full deliver.py --no-push passed server preflight at 917ede8673b. I then corrected TeX escaping in this report and reran the dry run before pushing the final version.
