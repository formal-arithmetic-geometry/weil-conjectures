# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-condensed-split-coset-induction.json: repaired split, statement unchanged; four assembly steps, 2399 characters in proof text.
- lem-sfb-condensed-tensor-induction-adjunction: statement-only, unsplit; no Mathlib match.
- lem-sfb-condensed-coset-tensor-normal-form: statement-only, unsplit; no Mathlib match.
- citations.json: verbatim statement quotations for every proof-step citation.

## Attachments

None. Read lean/Sheaf/CategoryTheory/CondensedSplitCosetInduction.lean: exists_datum at line 212 ends in sorry at line 217. Searches in lean/WeilConjectures for the blueprint tag and coset/induction notions found no project declaration proving the full item.

## Wanted

WANTED: an external reference for exact induction of internal modules over arbitrary condensed rings along a profinite subgroup with continuously split coset projection, for the item and both new nodes. The available source is agent-formulated, so no claim of a human-written reference is made. Stacks 03CY (sites-modules, lemma-sheafification-presheaf-modules) and 03EI (lemma-sheafification-exact) support module sheafification, not the entire condensed induction assertion.

## Earlier mathematical return repaired

The single return asks for the 7976-character proof to be distributed into at least two comparable, independently workable statement-only nodes, and an assembly at most 3000 characters without changing the statement. The adjunction node carries old steps 2--5 (balanced restrictions/action, functor laws, both transposes, sheafification equivariance, inverse laws and naturality); the normal-form node carries old steps 6--8 (continuous factorization into a section representative and a subgroup element, balanced inverse linear maps, restriction collisions and coefficient naturality). Old steps 1,9,10 remain the assembly: abelian action categories and underlying exactness, coefficientwise kernels followed by exact sheafification, and cokernels via the explicit adjunction universal property. The two extracted blocks are 2993 and 2153 characters in the returned proof, respectively. Their complete original arguments are preserved below for the workers who split the new nodes. Neither new node states exactness, so neither is a restatement of the whole item.

At the earlier mathematical-repair startup no split/report existed in the sandbox: it contained only dispatcher brief markers. Copied the current live returned item, including all metadata, its existing searches, Lean linkage and citations. The current live proof has the ten steps and lengths named in the return. No repository or launcher file was written, no git command was run, and no Lean was written or compiled.

## Current promotion return repaired (2026-10-22)

The present return is the landing refusal for branch head a825ed46c21, not a further mathematical rejection: the independent reader approved the delivery, but the side completion had not been promoted to the live DAG read by the queue. I continued the retained sandbox version rather than rebuilding the split or repeating its searches. The required initial dry run completed successfully at 42213708731 before any repair edit.

Compared the retained delivery with the current read-clone item field by field. Only proof, proof_deps and split_report differed: the current item still has the ten-step proof, and neither extracted node exists in the current DAG. Rebuilt the item from that current record, overlaying those three worker-owned fields, preserving the current statement, metadata, Lean linkage and maintainer review fields. The delivery command supplies the current server base in its isolated worktree; no git command was run in the read clone.

Re-read every existing statement dependency (sk-def-sfb-condensed-ring, def-weil-size-convention, def-sfb-condensed-action-module, def-weil-presheaf-modules-sheafification) and every existing proof dependency (lem-sfb-condensed-product-action-inflation, lem-sfb-internal-action-site-presentation, lem-weil-pbc-ringed-site-module-sheafification-exact), plus both retained new-node statements. All six citations remain verbatim in the current statements. In particular, the action-site statement uses the generated Grothendieck topology and explicitly disclaims composition of the image precoverage; the split needs only its final equivariant-sheafification, kernel, cokernel and zero-detection assertions, so uses none of the disclaimed property. The product-action statement explicitly permits a trivial factor; exact sheafification preserves finite limits on any ringed site. These hypotheses still match the profinite site and arbitrary condensed coefficient ring here.

Adjusted assembly step 1 to explain why the forgetful functor reflects exactness: it creates images and kernels, and detects invertibility of their comparison because its kernel and cokernel vanish precisely when their underlying objects vanish. This supplies the precise categorical justification without relying on faithfulness alone. No new node or new mathematical search question arises. The logged Mathlib queries and results were read and retained unchanged. Re-read the actual Rep adjunction and coinvariant finite-support equivalence: neither includes the internal sheaf coefficients or semilinear presheaf naturality. Repeated the current DAG/blueprint duplicate check and read the potentially related action-topos restriction and internal bar-resolution statements: geometric restriction with a right adjoint and a free bar module are different assertions from tensor induction with a left adjoint or the section-dependent normal form.

## Not duplicates

lem-sfb-condensed-tensor-induction-adjunction vs lem-sfb-condensed-split-coset-induction: proves the tensor construction and adjunction without a section; it does not assert exactness and is strictly smaller than the item.
lem-sfb-condensed-coset-tensor-normal-form vs lem-sfb-condensed-split-coset-induction: states a natural module-presheaf normal form, not a sheaf induction adjunction or exactness.
lem-sfb-condensed-tensor-induction-adjunction vs lem-sfb-internal-action-site-presentation: the latter supplies equivariant sheafification and kernels/cokernels for one group, but no induction between groups.
lem-sfb-condensed-tensor-induction-adjunction vs lem-sfb-condensed-product-action-inflation: the latter supplies product invariants and inflation, not tensor induction from a subgroup.

Before creating either node searched the whole DAG for coset, induction/restriction, tensor induction, and the proposed ids, and searched project Lean. Blueprint searches for coset returned only algebraic component cosets and central monodromy data; searches for induction restriction and tensor presheaf returned none. The broad induction search contains unrelated inductions; no blueprint statement states either extracted lemma. The ancestor command returns None, agreeing with the inherited null ancestor. No new Stacks-tag node is created.

## Mathlib searches

All new-node queries were executed using batch2/msearch.py and their actual logs retained in searches.jsonl. Adjunction searches include two semantic phrasings, Rep.indResAdjunction in Loogle, and grep for induction/free-forgetful adjunctions. Read Mathlib/RepresentationTheory/Induced.lean:53--171 and Condensed/Module.lean:34--58: the former is for an abstract group over a fixed commutative ring, and the latter is free/forgetful over a fixed ring; neither is internal subgroup induction over arbitrary A. LeanSearch's first adjunction query was rate-limited and is recorded unavailable. Normal-form searches include two semantic phrasings, Loogle for the expected tensor equivalence and the actual coinvariant finite-support map, a successful LeanSearch returning pullback/free/locally-constant results, and two grep queries. Read Coinvariants.lean:452--516: its equivalence concerns abstract representations and a fixed index type; the continuous coset factorization and natural semilinear restrictions with collapsing indices still need proof. No exact or one-line Mathlib specialization was found.

## Review by Q31

For the present promotion return, I performed the current-record comparison and dependency reading described above. Step 1 now includes the zero-kernel/zero-cokernel argument for reflecting isomorphisms, so the exactness criterion is explicit. The remaining three steps still use precisely the current statements quoted in citations.json. The normal-form inverses continue to cancel an unnormalized choice of section when H=P, and the kernel calculation works coefficient by coefficient even when restriction merges indices. The current closed-subgroup, arbitrary-ring and infinite-coset hypotheses require no adjustment. The two new nodes remain statement-only and absent from the current DAG. I re-read paragraph (3) of the current blueprint and Stacks 03CY/03EI; they justify the same provenance and sheafification tools as the earlier review, and do not supply a missing external induction reference. No repository or launcher file, Lean source, compiler or build tool was used for writing or building.

I read the current main-20261015 direct-images proof, paragraph (3), the chapter record sec-six-functors-basics and unit sk-thm-sf-ctf-stability. Paragraph (3) assembles open and proper direct images; it does not state this categorical input, as the original source metadata already admits. The two nodes retain that precise agent-written provenance and the outstanding reference request. I also read Stacks sites-modules.tex at lemma-sheafification-presheaf-modules (03CY) and lemma-sheafification-exact (03EI), and the full statements of every cited node.

Step 1 cites product-action inflation only for its abelian-category assertion, specializing one group to the trivial group. The closed subgroup is compact Hausdorff totally disconnected, so that assertion applies. The internal-action-site statement explicitly creates sectionwise kernels, sheafified cokernels, and detects zero; images are kernels of cokernels, which justifies reflection of exactness. The small-site and finite-limit hypotheses are those of the item, with trivial action on the coefficient ring.

Step 2 cites the new adjunction statement, whose hypotheses require only the same A,P,H and whose conclusions give the exact restrictions, left action, sheafification, map formula and both natural adjunction transposes. I checked balancing (ph)f(m)=p f(hm), scalar linearity, the unit formula, equivariance of the sheafified extension using the action-site equivalence, and the generator inverse laws against the retained original steps. The section is unused here.

Step 3 cites the normal-form statement, whose hypotheses explicitly introduce X,q,s and qs=1. It states the formulas for x_p,h_p and both inverse maps, and naturality for restrictions that merge indices and for equivariant coefficient maps; these are precisely what coefficientwise kernel identification needs. The action-site statement gives K(S)=ker(u_S), while exact module sheafification preserves this presheaf kernel. No claim that epimorphisms are sectionwise surjections occurs. The equivariant kernel comparison is created by forgetting, as that statement explicitly asserts.

Step 4 is the remaining elementary adjunction calculation, using the adjunction already obtained in step 2: naturality carries aLu=0 to bu=0, the original cokernel factors b uniquely, and inverse transposition gives the unique d. Additivity makes LvLu=0. This proves a cokernel universal property directly; kernel/cokernel pairs characterize short exact sequences in the abelian categories from step 1. No additional non-elementary fact is hidden in this step.

For B1--B7 both new nodes have empty proof and proof_deps and null proof_origin, introduce their own rings, groups, section modules and maps, cite the actual definition nodes, and use once-escaped TeX. Their statements contain conclusions and explicit formulas, not proof sketches. Source places identify the extracted original argument blocks and honestly state WANTED; Stacks labels were checked for the sheafification tool, without mislabelling the new theorems as Stacks results. The adjunction is a substantial construction/extension/naturality argument; the normal-form lemma has continuous factorization, tensor well-definedness, two inverses and presheaf naturality. Thus these are the separate proof tasks requested by the human, not elementary one-line nodes.

For section E I checked H=P (X a point, allowing a section with s(*) different from 1), H=1 (arbitrary infinite profinite X=P), P trivial, a non-normal subgroup of a finite group, A the zero ring, and the empty test space. The factorization h_p=s(qp)^{-1}p lies in H without normality. If S is empty then C(S,X) is singleton and both tensor and finite-support formulas still apply (the coefficient sheaf has the required empty-cover behavior). For a map of test spaces that collapses two distinct coset maps, coefficients add; naturality of h_p under precomposition makes the normal-form restrictions agree. For H=P, the twist by the chosen section cancels between alpha and beta, so no normalized section was silently assumed. For a zero module the normal form is zero. These checks preserve the infinite-index, non-discrete and arbitrary-ring clauses. No statement dispute was found and the item's statement remains byte-for-byte unchanged.

The repair replaces none of the old reasoning by an unexplained summary: all ten original steps follow below, with their new locations. The extracted nodes are unsplit so their proof arguments belong here, not in their JSON proof fields. No new proof step exceeds 2000 characters. No SGA source or off-unit route was introduced. Nothing remains mathematically unfinished beyond the two intentionally unsplit tasks.

## Retained original arguments and allocation

### Original step 1 → assembly step 1

Use the section-module interpretation of [def-sfb-condensed-action-module]. The subgroup $H$ is profinite: it is closed in the compact Hausdorff group $P$, and its subspace topology has the inherited clopen basis. For $J=H,P$ apply [lem-sfb-internal-action-site-presentation] on the specified small profinite site with $K(S)=C(S,J)$ and ring sheaf $A$. This site has finite limits and the given finite jointly surjective covers; $K$ is the condensed group of $J$ and acts trivially on $A$. The cited statement gives equivariant sheafification and says that forgetting the action creates kernels and cokernels, with sectionwise kernels and sheafified sectionwise cokernels. It also detects zero objects. The categories are abelian by [lem-sfb-condensed-product-action-inflation], taking its first group to be $J$ and its second group trivial. Thus exactness can be checked on underlying module sheaves: the image is the kernel of the cokernel, so both image and kernel are created by forgetting, and equality is reflected by the faithful forgetful functor.

Original citations: def-sfb-condensed-action-module, lem-sfb-internal-action-site-presentation, lem-sfb-condensed-product-action-inflation.

### Original step 2 → lem-sfb-condensed-tensor-induction-adjunction

Write $B_M(S)=A(S)[P_S]\otimes_{A(S)[H_S]}M(S)$. Its elements are finite sums of symbols $a[p]\otimes m$, modulo additivity and the balancing relations $[ph]\otimes m=[p]\otimes h m$ and $a[p]\otimes m=[p]\otimes am$. Restriction along $t:T\to S$ sends such a symbol to $t^*a[p\circ t]\otimes t^*m$; naturality and linearity of the $H$-action preserve both relations. Left multiplication $g([p]\otimes m)=[gp]\otimes m$ also preserves them, is $A(S)$-linear, and is natural in $S$. Its unit and associativity laws follow from $1p=p$ and $g(g'p)=(gg')p$. The equivariant sheafification assertion of [lem-sfb-internal-action-site-presentation], together with [def-weil-presheaf-modules-sheafification], therefore makes $B_M^\#$ the claimed internal $P$-module. A morphism $u:M\to M'$ acts by $[p]\otimes m\mapsto[p]\otimes u(m)$ before sheafification. Identity, composition, zero and sums of maps have these same formulas; the sheafified maps retain them by uniqueness of their extensions. Hence this is an additive functor $L=\operatorname{Ind}_H^P$.

Original citations: lem-sfb-internal-action-site-presentation, def-weil-presheaf-modules-sheafification.

### Original step 3 → lem-sfb-condensed-tensor-induction-adjunction

Let $\eta_M:B_M\to L M$ be the sheafification unit. For a $P$-equivariant linear map $F:L M\to N$ define $\Phi(F)_S(m)=F_S(\eta_M([1]\otimes m))$. These maps are linear and commute with restriction. For $h\in H_S$, balancing gives $[1]\otimes hm=[h]\otimes m=h([1]\otimes m)$, so $\Phi(F)(hm)=h\Phi(F)(m)$. Thus $\Phi(F)$ is a morphism $M\to\operatorname{Res}_H^P N$, with precisely the forward formula in the statement.

Original citations: elementary.

### Original step 4 → lem-sfb-condensed-tensor-induction-adjunction

Conversely let $f:M\to\operatorname{Res}_H^P N$ be equivariant. On $B_M(S)$ define $\widetilde f([p]\otimes m)=p f(m)$ and extend linearly to finite sums. It respects balancing since $(ph)f(m)=p f(hm)$, and it respects scalar balancing since every $p$ acts $A(S)$-linearly. These maps commute with restriction, and $\widetilde f(g([p]\otimes m))=gp f(m)=g\widetilde f([p]\otimes m)$. By [def-weil-presheaf-modules-sheafification] there is a unique linear extension $\Psi(f):L M\to N$. It is $P$-equivariant: under the equivalence of [lem-sfb-internal-action-site-presentation], $\widetilde f$ is a module-presheaf map on the action site $C_K$, and its extension by the module-sheafification universal property on $C_K$ corresponds to an equivariant map whose underlying extension on the base site is the same unique linear extension. This uses the cited statement's identification of the two sheafifications, including their units.

Original citations: def-weil-presheaf-modules-sheafification, lem-sfb-internal-action-site-presentation.

### Original step 5 → lem-sfb-condensed-tensor-induction-adjunction

We have $\Phi\Psi(f)(m)=1f(m)=f(m)$. On every presheaf generator, $\Psi\Phi(F)(\eta_M([p]\otimes m))=pF(\eta_M([1]\otimes m))=F(\eta_M([p]\otimes m))$. The universal property in [def-weil-presheaf-modules-sheafification] makes the resulting sheaf maps equal. For a source map $u:M'\to M$ and a target map $v:N\to N'$, the formula gives $\Phi(vFu)(m)=v\Phi(F)(u(m))$, where on the left $u$ denotes $L u$. This proves naturality of the inverse bijections, hence the asserted adjunction $L\dashv\operatorname{Res}_H^P$ with both specified formulas. No property of $s$ was used for the adjunction.

Original citations: def-weil-presheaf-modules-sheafification.

### Original step 6 → lem-sfb-condensed-coset-tensor-normal-form

Now use the continuous section to prove preservation of kernels. Put $X_S=C(S,X)$. Every $p\in P_S$ has a unique expression $p=(s\circ x)h$ with $x\in X_S$ and $h\in H_S$: necessarily $x=q\circ p$ and $h=(s\circ q\circ p)^{-1}p$. The latter map has image in $H$ because $p$ and $s(q(p))$ belong to the same right coset. It is continuous as a map to $H$ with its subspace topology, since its composite to $P$ is continuous. Conversely $(x,h)$ has product $(s\circ x)h$ with coset $x$, and these two formulas are inverse. They commute with precomposition by every map of profinite test sets. No normality or finite index of $H$ is used.

Original citations: elementary.

### Original step 7 → lem-sfb-condensed-coset-tensor-normal-form

Define $D_M(S)=\bigoplus_{x\in X_S}M(S)$, whose elements have finite support, and write $e_x(m)$ for an element supported at $x$. The maps
$$\alpha_S:B_M(S)\longrightarrow D_M(S),\qquad [p]\otimes m\longmapsto e_{qp}\bigl(((s\circ qp)^{-1}p)m\bigr),$$
$$\beta_S:D_M(S)\longrightarrow B_M(S),\qquad e_x(m)\longmapsto[s\circ x]\otimes m$$
are inverse $A(S)$-linear maps. Indeed the factorization of $ph$ is $(x,h_p h)$ if that of $p$ is $(x,h_p)$, so $\alpha_S([ph]\otimes m)=e_x(h_p h m)=\alpha_S([p]\otimes hm)$; scalar balancing follows from linearity of the $H_S$-action. This verifies that $\alpha_S$ is defined on the tensor product. The map $\beta_S$ is linear on each summand, so defines a linear map on finite-support sums. The two composites on generators are
$$e_x(m)\longmapsto e_x(m),\qquad [p]\otimes m\longmapsto[s\circ qp]\otimes h_p m=[p]\otimes m.$$
Additivity then proves both identities on all elements.

Original citations: elementary.

### Original step 8 → lem-sfb-condensed-coset-tensor-normal-form

Give $D_M$ restriction maps $e_x(m)\mapsto e_{x\circ t}(t^*m)$ along $t:T\to S$, adding coefficients when distinct indices become equal after restriction. The factorization in step 6 shows that $\alpha,\beta$ commute with these restrictions, even when indices merge. They are also natural in equivariant maps $M\to M'$, since such a map commutes with every $h_p$. Thus $B_M\cong D_M$ as module presheaves, naturally in $M$. This assertion concerns finite-support sums indexed by continuous maps $S\to X$; it does not identify them with a product, nor with a sum indexed by individual points of $X$.

Original citations: elementary.

### Original step 9 → assembly step 3

For an equivariant map $u:M\to N$, let $K=\ker u$. By [lem-sfb-internal-action-site-presentation], $K(S)=\ker u_S$. Under the normal forms of steps 7--8, $B_u(S)$ applies $u_S$ to each coefficient, so its kernel consists exactly of finite-support sums with coefficients in $K(S)$. The inclusion $B_K(S)\to B_M(S)$ is injective and identifies $B_K$ with the presheaf kernel of $B_u$, naturally in $S$. Apply [lem-weil-pbc-ringed-site-module-sheafification-exact] to the ringed profinite site $(C,A)$. It preserves this kernel, so the underlying module sheaf of $L K$ is the kernel of the underlying map $L u$. The comparison is $P$-equivariant by construction in step 2; the action-site kernel assertion identifies it with the equivariant kernel as well. Consequently $L$ preserves kernels. This uses exact sheafification only for a sectionwise kernel diagram, and does not assume that epimorphisms of condensed modules are surjective on sections.

Original citations: lem-sfb-internal-action-site-presentation, lem-weil-pbc-ringed-site-module-sheafification-exact.

### Original step 10 → assembly step 4

Let $u:M'\to M$ and let $v:M\to Q$ be its cokernel in the abelian action category of step 1. A map $a:L M\to N$ with $aL u=0$ corresponds by the natural adjunction of step 5 to a map $b:M\to\operatorname{Res}N$ with $bu=0$. There is a unique $c:Q\to\operatorname{Res}N$ with $cv=b$; its adjoint $d:L Q\to N$ is the unique map with $dL v=a$, by the same naturality. Also $L v L u=L(vu)=0$ by additivity. This is the cokernel universal property, so $L$ preserves cokernels. Finally, in a short exact sequence $0\to M'\xrightarrow{u}M\xrightarrow{v}M''\to0$, $u$ is the kernel of $v$ and $v$ is the cokernel of $u$. Steps 9 and 10 preserve both descriptions, which proves that the induced sequence is short exact. All finite-support formulas allow arbitrary $X_S$ and arbitrary section modules, establishing the last clause as well.

Original citations: elementary.

