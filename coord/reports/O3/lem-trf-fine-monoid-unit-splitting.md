# Worker report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-fine-monoid-unit-splitting.json: unchanged statement; four assembly steps, below 3000 characters.
- dag/nodes/sec-trace-formula/lem-trf-integral-sharpening-group-exactness.json: statement, unsplit, no Mathlib match; original step 1 and finite generation of the sharp completion in step 2.
- dag/nodes/sec-trace-formula/lem-trf-group-section-monoid-product.json: statement, unsplit, no Mathlib match; original steps 3--5 under the more general hypotheses of a surjective integral-monoid map, kernel equal to units, and a finite basis of the target completion.
- dag/nodes/sec-trace-formula/lem-trf-fine-monoid-unit-generators.json: statement, unsplit, no Mathlib match; original step 6's unit-sublist and torsion arguments.
- citations.json: exact statement quotations for all five proof citations. searches.jsonl: actual msearch results, retained verbatim. No Lean or repository files written; no compiler, Lake or local DAG checks run.

## Attachments

None. Searched WeilConjectures/ for the exact blueprint tag, the theorem name, sharpening, units, group completion and splitting; no finished matching declaration was found. Read lean/Sheaf/GroupTheory/FineMonoidUnitSplitting.lean: the exact theorem ends with sorry. It cannot close the item.

## WANTED

None. The ILO volume is present. All three extracted statements are explicitly labelled agent algebraic refinements, not falsely attributed as verbatim ILO theorems.

## Returned issue and repair

The return requires spreading the 3188-character proof over at least two new statement-only nodes rather than merely abbreviating it. The sandbox initially contained only dispatcher brief markers, no node, report or search log. I therefore copied the current repository item, preserving its statement, proof_origin, all Lean records, reviewed records and ancestry. No earlier sandbox argument or search was discarded. The three work packages have independent arguments (exactness; lifting and positive restriction; unit generators), not one renamed version of the original theorem. Every original argument is accounted for below. No statement dispute or unit-route departure arose. The finite-basis theorem remains the existing Mathlib leaf; no duplicate child was made for it.

## Unfinished work

The three new nodes deliberately have status unsplit, empty proof/proof_deps and null proof_origin. Their proofs are work for independent future workers. This delivery completes only the requested one-level stage-1 split.

## Sources and searches

Read ILO VIII 3.1.1--3.1.3 (printed p.98), 3.1.9--3.1.11 (pp.99--100) and 3.1.24--3.1.28 (p.102). These supply the unit/sharpening conventions and the local-lift comparison context, but do not state the extracted algebraic lemmas. Read VI 3.7(a), printed p.75: the exact sequence (3.a), its splitting for a finitely generated torsion-free sharp group, and restriction of that section to the sharp monoid motivate the second child. The explicit elementary proofs below are the retained agent refinement. No SGA source is used. No Stacks result is asserted or quoted by a section number.

For each new node ran LeanFinder twice with different phrasing, Loogle with the expected names, source grep, and LeanSearch. Read each returned type and the relevant source in Mathlib/GroupTheory/MonoidLocalization/{GrothendieckGroup,Finite}.lean and Mathlib/LinearAlgebra/FreeModule/PID.lean. LeanSearch was unavailable (HTTP rate-limit result), recorded as unavailable. GrothendieckGroup.lift and instFG do not state the first child's kernel identification; group-extension Section lemmas do not restrict to a positive monoid; Associates.prod_mk evaluates products, not a direct product decomposition; number-field unit finite generation has different hypotheses; trivial-unit irreducible generation does not state the unit-sublist theorem. None of the children is an exact match or one-line specialization of those results. The existing leaf Module.basisOfFiniteTypeTorsionFree' is confirmed at PID.lean:383. The parent's earlier Mathlib search history is retained unchanged.

Whole-DAG searches used the monoid/sharp completion, kernel, group section, unit generating list and source-place concepts. Whole imported-blueprint searches were run with blueprint_refs.py for sharpening, group completion, group section, unit generators, unit subgroup and sharpening group; no node states any new lemma. blueprint_refs.py ancestor identifies lem-trf-local-term-locality; each child inherits the existing historical local-lift ancestry with this item prepended to via. The chapter and unit were read; their route and realization records are unchanged.

## Not duplicates

- lem-trf-integral-sharpening-group-exactness vs lem-trf-fs-face-sharpening: the existing lemma assumes saturated Q and localizes at a face; this child applies to every integral P, with neither saturation nor sharp-completion torsion-freeness, and gives the actual kernel map and images of a specified generating list.
- lem-trf-integral-sharpening-group-exactness vs lem-trf-face-localization-units: the existing lemma computes units of a face localization; it does not identify the completion of a quotient by units.
- lem-trf-integral-sharpening-group-exactness vs def-trf-fine-fan-blowup: the definition supplies unit/sharpening conventions, not the injectivity and exactness assertions.
- lem-trf-group-section-monoid-product vs lem-trf-fine-monoid-unit-splitting: the child assumes an explicit finite basis and exactness for an arbitrary integral-monoid quotient, and proves the intermediate section and inverse formulas; it assumes no fineness or torsion-freeness and does not prove units finite free. Those separate arguments are indispensable to the parent.
- lem-trf-group-section-monoid-product vs lem-trf-fs-chart-free-factorization: the existing lemma assumes saturated chart monoids and an injective map on completions, and gives a free positive-chart factorization; our map is surjective with kernel units and the result is a monoid product.
- lem-trf-group-section-monoid-product vs lem-per-tame-unit-extension-character: the existing lemma needs a strictly henselian ring, a tame group action, and an fs sharp positive cone; it gives an equivariant character statement, not this integral-monoid product.
- lem-trf-fine-monoid-unit-generators vs lem-trf-fg-torsionfree-group-free: the leaf assumes finite generation and proves a basis; this child proves finite generation of units from a specified monoid generating list, and does not prove a basis.
- lem-trf-fine-monoid-unit-generators vs lem-trf-face-localization-units: the existing lemma identifies units after localization but gives no finite generating sublist.
- lem-trf-fine-monoid-unit-generators vs def-trf-fine-fan-blowup: the definition says P is finitely generated, not that its subgroup of units is generated by the unit sublist.

## Review by O3

I read the source passages above with the item and the three new statements open. I checked delivery-errors B--E: every object and hypothesis is introduced; the children carry statements only, not proof sketches; all their notions are defined inline or by the two existing definition nodes, which I read in full. TeX is single-escaped after JSON decoding. Sources are the actual present ILO volume with precise places and explicit attribution as agent refinements. The two torsion-free hypotheses on the item are unchanged. No saturation was silently assumed. The new nodes are distinct proof tasks of comparable scope, not elementary corollaries of nodes already cited. They separate arguments the human explicitly asked to parallelize.

Assembly step 1 cites the new exactness statement, whose statement explicitly gives integrality of B, surjectivity and the kernel of pi, and the images generating H. The fineness hypothesis on P supplies the finite list; it is not used to infer saturation. Step 2 cites the existing finite-basis leaf for precisely finitely generated torsion-free H, then the second child's statement for the section and both inverse formulas. I verified all of that child's hypotheses: P is integral by fineness, B by step 1, q is the defining surjective quotient, pi has the asserted kernel by step 1, and the leaf gives the finite basis. Step 3 cites the unit-generator child for both finite generation and inherited torsion-freeness of U, then the leaf for exactly a finite integer basis of U. The coordinate isomorphism and its inverse are written out. Step 4 only composes the already obtained inverse maps with the coordinate isomorphism; both inverse and first-projection equations are displayed. No unproved non-elementary fact is hidden in that composition. citations.json quotes each cited statement verbatim, and proof_deps is exactly the union of uses.

Small cases checked: P=0 (all lists/bases empty); P an abelian group (B=0, all generators units, t=0 and the product is U); P sharp (U=0); the nonsaturated sharp monoid generated by 2 and 3 in N (no saturation needed); and P=N plus Z with list (1,0),(0,1),(0,-1) (unit sublist is exactly the two latter generators). The exactness child also allows torsion, e.g. P=Z/2, and does not falsely assert a free completion. The section child has a finite-free target as a hypothesis, so the familiar failure with torsion sharp completion does not apply. If q is identity its kernel must be the zero unit group; for a sharp monoid the resulting section is identity. For the unit sublist, repeated generators and zero cause no issue; zero is a unit and empty sums give zero.

I also checked the two missing-hypothesis counterexamples recorded in the prior review: P=Z/2 would contradict free units without torsion-freeness of Pgp; P generated by (2,0),(-2,0),(0,1),(1,1) in Z² has U=2Z times 0 and Bgp=Z/2 plus Z, so its sharp completion has no finite integer basis. The new conditional statements do not accidentally claim splitting in that case. No child references the parent, and all three are in the same chapter and unit. No step is longer than 2000 characters, and the whole parent is shorter than 3000.

## Full retained arguments for the new workers

The following is the original proof, copied verbatim so that extraction loses no argument. It is report material only; none of the unsplit node statements contains a proof. Original step 1 and the first part of step 2 belong to the exactness child. Original steps 3--5 belong to the quotient/section child. Original step 6's generator and torsion arguments belong to the unit-generators child. Applications of the already existing finite-basis leaf in original steps 2 and 6 and composition with its coordinate map remain explicit in the parent assembly.

### Original step 1

Put $G=P^{\rm gp}$. By integrality regard $P$ as a submonoid of $G$; $U=P^\times$ is a subgroup since the inverse of a unit lies in $P$. Let $q:P\to B$ be the quotient. The map $B\to G/U$, $q(p)\mapsto p+U$, is well defined and injective: equality of cosets means $p-p'\in U$, which is exactly equality modulo addition of a unit. Thus $B$ is integral. Write $H=B^{\rm gp}$ and let $\pi:G\to H$ send $p-p'$ to $q(p)-q(p')$. It is surjective because every element of $H$ is such a difference. Since $B$ embeds in its group completion, $\pi(p-p')=0$ exactly when $q(p)=q(p')$, equivalently $p-p'\in U$. Therefore $\ker\pi=U$. These are direct checks from the group presentation and the unit equivalence relation, not an appeal to an uncited exactness theorem.

### Original step 2

Choose a finite monoid generating list $a_1,\ldots,a_d$ for $P$. The elements $q(a_i)$ generate $B$, so their images generate $H$ as an abelian group: expand each difference of elements of $B$ into integer combinations of those images. The hypothesis says that $H$ is torsion free. Apply [lem-trf-fg-torsionfree-group-free] to obtain a finite basis $e_1,\ldots,e_r$ of $H$.

### Original step 3

For each basis element choose $g_i\in G$ with $\pi(g_i)=e_i$, using the surjectivity proved in Step 1. Define $t:H\to G$ by $t(\sum_i n_i e_i)=\sum_i n_i g_i$. Unique basis coordinates make this well defined and additive, and the displayed formula gives $\pi\circ t=1_H$. This constructs the required group section explicitly, without invoking a separate splitting theorem. When $r=0$ the sums are empty and $t$ is the zero homomorphism.

### Original step 4

For $b\in B$ choose $p\in P$ with $q(p)=b$. In $G$ the difference $t(b)-p$ has image $b-b=0$ under $\pi$, hence belongs to $U$ by Step 1. Every unit belongs to $P$, so $t(b)=p+(t(b)-p)$ belongs to $P$. Define $j(b)=t(b)$, now with codomain $P$. This definition is independent of the chosen $p$, since it is the restriction of the fixed map $t$. Additivity and $j(0)=0$ follow from $t$, and $q(j(b))=b$ follows from $\pi t=1$ and the embedding $B\subset H$. Thus $j$ is a monoid section.

### Original step 5

Define $F:B\oplus U\to P$ by $F(b,u)=j(b)+u$ and $E:P\to B\oplus U$ by $E(p)=(q(p),p-j(q(p)))$. The second coordinate of $E(p)$ lies in $\ker\pi=U$. Both maps preserve addition and zero. Direct substitution gives $F(E(p))=p$ and $E(F(b,u))=(b,u)$, since $q(u)=0$ and $qj=1$. They are inverse monoid isomorphisms. Moreover $q(F(b,u))=b$, so the quotient is the first projection, with the specified copy of $U$ preserved.

### Original step 6

It remains to identify $U$ with $\mathbf Z^s$. In the generating list from Step 2, every generator occurring with positive coefficient in an expression $u=\sum_i n_i a_i$ for a unit is itself a unit: if $u=a_i+v$, then $a_i+(v-u)=0$ and $v-u=v+(-u)$ lies in $P$. Hence the sublist consisting of the $a_i$ that are units generates $U$ as a monoid, and in particular as an abelian group. It is torsion free because it is a subgroup of the assumed torsion-free group $G$. Apply [lem-trf-fg-torsionfree-group-free] to $U$ to obtain a finite basis of length $s\geq0$. Its integer-coordinate map is an isomorphism $U\simeq\mathbf Z^s$. Composing its product with $1_B$ with Step 5 proves both formulations of the statement.

