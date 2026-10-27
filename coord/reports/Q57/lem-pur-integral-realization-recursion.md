# Q57 stage-1 re-split: lem-pur-integral-realization-recursion

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-integral-realization-recursion.json: statement and stmt_deps unchanged; 2,464-character assembly proof.
- dag/nodes/sec-smooth-purity/lem-pur-unary-counit-transpose.json: statement, unsplit; no Mathlib match. Unary coefficient transpose, actual-unit normalization, inverse-factor and naturality identities.
- dag/nodes/sec-smooth-purity/lem-pur-binary-counit-transpose.json: statement, unsplit; no Mathlib match. Independent-input bifunctor coefficient transpose, inverse-factor and naturality identities.
- citations.json: verbatim statement excerpts for every citation in every assembly step.

## Attachments

None. Searching the blueprint id and realization-recursion notions in lean/WeilConjectures found no full attachment. lean/Sheaf/SixFunctors/IntegralRealizationRecursion.lean:233 states the item but its proof ends in sorry at line 254; the full declaration is WeilConjectures.IntegralSystemRealization.Recursion.integralRealizationRecursion. It is not a completed proof.

## WANTED

None. These are agent-formulated categorical refinements of a blueprint coefficient-transport construction, not purported verbatim literature theorems. No SGA source is used.

## Repair order and previous deficiencies

The released stage-1 keep_plan repair note dated 2026-10-22 overrides the old split/review state and requires at least two comparable new statement-only nodes, preserving the statement and spreading all the original arguments. I extracted the two substantial categorical arguments, rather than duplicating the item or moving it wholesale into another node. The two new statements concern arbitrary categories, arbitrary specified comparison d and arbitrary coefficient arrows q; they contain no expression-tree theorem, no integral scheme domain, no six-functor realization, and no assertion of the item's full conclusion. Invertibility/reconstruction and existence of the coefficient-recursive family already have stronger existing nodes and are cited rather than duplicated. The short residual tree induction is assembly.

## Not duplicates

lem-pur-unary-counit-transpose vs lem-pur-adjoint-equivalence-conjugation-calculus: the latter fixes barred F=LFR and transports an adjunction F⊣G, its counit and transformations; the new statement allows an independently specified barred A and d, and calculates the transpose of A(q)r_A and its inverse-factor naturality.
lem-pur-unary-counit-transpose vs lem-trf-counit-realization-substitution: that node is about actual scheme pullback/scalar-change model maps and chi-normalized scalar associativity; it does not give the arbitrary categorical specified-d transpose of a coefficient arrow.
lem-pur-binary-counit-transpose vs lem-pur-expression-counit-substitution-coherence: that node assumes primitive comparison isomorphisms on normalized systems and proves expression substitution/context laws; the new statement calculates the primitive two-input adjunction transpose itself.
lem-pur-binary-counit-transpose vs lem-sf-integral-expression-recursion: the latter is scheme-specific existence and reduction equality for finite expressions, assumes invertibility on the complete/normalized domains, and has no arbitrary-q bifunctor transpose or inverse-factor naturality formula. The existing expression node is reused for assembly, not recreated.
lem-pur-unary-counit-transpose vs lem-sf-integral-expression-recursion: the same domain distinction applies, and the unary new statement includes transpose/inverse-factor laws for arbitrary q with no finite expression or coefficient sheaf assumptions.
lem-pur-binary-counit-transpose vs lem-pur-normalized-tensor-constraint-transport: the latter identifies tensor constraints built on quotient/Roos models; the new statement is about arbitrary bifunctors without a monoidal structure and does not identify those geometric constraints.

The whole DAG was searched for transpose, counit substitution, d_A/naturality and binary formulas; blueprint_refs searches 'adjunction transpose', 'expression recursion', 'counit substitution', 'binary functor', and 'counit transport' were read. The six blueprint hits for 'adjunction transpose' concern other geometric maps, not these formulas. The nearest relevant statements above were opened. Neither new node has a Stacks tag: the source is the agent-formulated blueprint refinement, so there are no same-tag duplicate pairs. Their blueprint ancestry retains thm-pur-rational-and-qbar-purity via this item and its two inherited ancestors.

## Review by Q57

I read AGENTS.md, worker/brief/stage-1 instructions, GOAL.md, the three blueprint levels in SETUP.md, both copies of delivery-errors B–E, the item and its released repair note, the smooth-purity chapter and compatibility unit, and main-20261015 fix-prop-coherence.proof.md. That proof's maps-used sentence concerns coefficient compatibility of evaluation and actual adjunction units/counits; the explicit recursive interface is an agent expansion, correctly labelled as such. For both new nodes I used the original seven-step argument as the immediate source and checked the equations against the actual categorical definitions. Mathlib Basic.lean:226–266 gives Hom-equivalence naturality; Basic.lean:279–299 gives triangles and unit naturality; Mates.lean:84–131 and 285–295 gives mates/counit formulas. Those are ingredients, not a one-line specialization proving the whole stated conjunction; no searched hit identifies the arbitrary specified d together with transpose, inverse comparison, and input naturality. All search records come from the actual msearch log, including the second phrasings. Completed interrupted searches were recovered from searches.jsonl before any further calls.

Assembly step 1 uses the reconstruction statement's actual invertible unit/counit, without a boundedness restriction; our domain is narrower and satisfies it. The calculus statement supplies the actual reduction functor/adjunction, not just a levelwise assignment. No equality is detected by evaluation. Step 2 uses the expression-recursion statement's explicit r-recursion and reduction equation, and the generator statement's exact r_A=e R(d_A^-1), including the specified open d. All intermediate bounds, origins and completeness are those expressly required in the item. The expression node assumes the same specified primitive identifications; here d is exactly the generator identification, as required by the item and the parent construction.

Step 3 uses the new unary and binary statements verbatim at arbitrary q_V,q_T. Every arrow was type-checked on paper: q:R I→M, b:I→LM, r:R(bar A I)→A(RI), and b_A:bar A I→LA M. In the binary statement the three adjunctions are at the two input schemes and output scheme. The inverse order is correct: inverse of L A(e) d^-1 bar A(b) is bar A(b^-1) d (L A(e))^-1. For tensor the product-category functor preserves inverse pairs; no flatness or exactness is smuggled in. Step 4 uses the existing realization statement for the specified family and the expression node's actual coefficient equality r=e R(c^-1) to identify its transpose. This improves the old argument, which reached into the parent proof to identify its normalization; the required coefficient equation is now an explicit cited statement. Finite-tree induction starts at the actual u and treats both smaller tensor children; uniqueness follows at each parent by the fixed formulas, so no hidden tree theorem is delegated. Step 5 cites the exact new naturality laws; inverse-unit naturality and pasting child squares finish the induction.

Small cases: with all functors and adjunction maps identities the unary and binary transpose identities reduce to functoriality and q=b, without forcing d to be an identity. With q=1 the transpose is the actual unit, so arbitrary automorphism choices are excluded. With f or g identity the two-input naturality reduces to the correct one-slot square; both identity maps give the identity equation. Empty categories make universal assertions vacuous; no objects are chosen. Repeated inputs are allowed. For the geometric assembly zero complexes and empty open extensions give zero maps; the single-leaf tree gives u^-1; one operation on R[0] gives the specified d by the triangle identity. No n=0 or shift assertion is introduced.

B–E checks: each new statement introduces all categories, functors, transformations, triangles and maps; each is statement-only with proof=[], proof_deps=[], proof_origin=null, unsplit status, and complete source/blueprint/search metadata. No hollow data, false statement, circular dependency, new coefficient-category identification or added hypothesis is used. Statement dependencies on categories are explicit; other categorical data are defined inline. No new step exceeds 2,000 characters. Existing reconstruction and expression nodes do not reach this item, as checked by dependency traversal. New nodes depend only on the category definition. The inherited reviewed and Lean metadata are retained as history; this delivery requests a fresh stage-1 review, not reuse of the old approval.

## Preservation of all seven original arguments

The original argument is reproduced verbatim below so that the split never loses an equation or its justification. These are report notes only, not proof sketches hidden inside unsplit node statements.

Allocation: original step 1 is already the statement of lem-pur-normalized-actual-reconstruction-maps (including actual level counit and completeness); original step 2's triangle/naturality argument is additionally an explicit clause of the unary new node. Original step 3's transposition and basic normalization are in both new nodes (unary and binary), its coefficient recursion in the existing expression node. Step 4 is exactly the unary new node. Step 5 is exactly the binary new node. Step 6's invertibility is supplied by those new nodes, coefficient identification by the existing expression node, and finite-tree uniqueness remains the written short assembly. Step 7's inverse-factor equations and unary/binary naturality are explicit conclusions in the corresponding new nodes; pasting and all edge checks remain in assembly and this report. This allocation avoids creating duplicates for the two arguments that already have their own nodes.

### Original step 1

For a normalized system $M$, [lem-coef-normalized-dvr-effectivity] says that the canonical counit comparisons $(\mathcal LM)\otimes^L_R A_n\to M_n$ are isomorphisms and that $\mathcal LM$ is derived complete. These are precisely the evaluations of the actual $e_M$ of [lem-coef-derived-system-evaluation-calculus]. The latter statement detects isomorphisms by derived evaluations, so $e_M$ is invertible in $D(\mathscr S_W)$. This is detection of isomorphisms, with no assertion about detecting equality. Its evaluated isomorphisms identify the reductions of $\mathcal LM$ with the levels of $M$, so they also give constructibility and exactly the assumed common cohomological and Tor bounds. Thus every use of $d_A(\mathcal LM)$ below has the stipulated integral input and normalized-system hypotheses.

Original cited nodes: lem-coef-normalized-dvr-effectivity, lem-coef-derived-system-evaluation-calculus

### Original step 2

The right triangle identity from [lem-coef-derived-system-evaluation-calculus] gives $\mathcal L(e_M)u_{\mathcal LM}=1$, hence $u_{\mathcal LM}=\mathcal L(e_M)^{-1}$. For an allowed integral $K$, its reduction $\mathcal RK$ is one of the normalized input systems in the hypotheses. The variable-expression case of [lem-sf-integral-compactification-system-realization] supplies an isomorphism $h:\mathcal L\mathcal RK\to K$. Only existence of this isomorphism is used here, not its normalization. Naturality gives $u_Kh=\mathcal L\mathcal R(h)u_{\mathcal L\mathcal RK}$. All factors on the right and $h$ are invertible, so the specified actual unit $u_K$ is invertible. This avoids identifying an arbitrary Roos-triangle lift with the actual unit.

Original cited nodes: lem-coef-derived-system-evaluation-calculus, lem-sf-integral-compactification-system-realization

### Original step 3

Write $I_V=V_{\rm int}(K_i)$ and $M_V=V(\mathcal RK_i)$. Unpack the coefficient construction of the specified realization: at a variable its coefficient map is $q_{K_i}=1_{\mathcal RK_i}$; at a unary or tensor node it is the successive composite of the canonical single-operation coefficient maps:
$$q_{AV}=A(q_V)r_A(I_V),\qquad q_{V\otimes T}=(q_V\otimes^Lq_T)r_\otimes(I_V,I_T).$$
These are definitions of the composite comparison, not a claim that finite evaluations determine it. The single-operation maps are the actual system maps $r_A=e_{A\mathcal RI}\mathcal R(d_A(I)^{-1})$ of [lem-sf-generator-reduction-coherence], with its specified localized open comparison. Under the adjunction of [lem-coef-derived-system-evaluation-calculus] the transpose of $q_V:\mathcal RI_V\to M_V$ is
$$b_V=\mathcal L(q_V)u_{I_V}:I_V\to\mathcal LM_V,$$
and the inverse transposition formula is $q_V=e_{M_V}\mathcal R(b_V)$. Indeed substitution reduces this equality to naturality of $e$ and $e_{\mathcal RI_V}\mathcal R(u_{I_V})=1$. At a single operation the transpose is $d_A(I)^{-1}$: substitute the displayed $r_A$, move $\mathcal R(d_A^{-1})$ past the unit, and cancel $\mathcal L(e_N)u_{\mathcal LN}=1$ for $N=A\mathcal RI$. This fixes the basic normalization, including $J_j$. At a leaf $b_{K_i}=u_{K_i}$, so the realized comparison there is $b_{K_i}^{-1}=u_{K_i}^{-1}$.

Original cited nodes: lem-sf-generator-reduction-coherence, lem-coef-derived-system-evaluation-calculus

### Original step 4

Suppose the inverse comparison $b_V:I_V\xrightarrow{\sim}\mathcal LM$ has been constructed for a smaller tree, with $M=M_V$. Transpose the unary coefficient composite in step 3. The single-operation transpose calculated there first gives
$$b_{AV}=\mathcal LA(q_V)d_A(I_V)^{-1}.$$
Substitute $q_V=e_M\mathcal R(b_V)$ and then use naturality of $d_A$ at $b_V$ to obtain
$$b_{AV}=\mathcal LA(e_M)\,d_A(\mathcal LM)^{-1}\,A_{\rm int}(b_V).$$
Each factor is invertible, by steps 1-2 and the stipulated single-operation isomorphism. Inverting this equality, in reverse order, gives
$$b_{AV}^{-1}=A_{\rm int}(b_V^{-1})\,d_A(\mathcal LM)\bigl(\mathcal LA(e_M)\bigr)^{-1}.$$
The last two factors are exactly $a_A(M)$ in the statement. The common bounds and compatible origin witnesses are those explicitly required of this intermediate system; $I_V\cong\mathcal LM$ also ensures that $d_A(I_V)$ is used on a complete constructible input. This calculation treats each of $P_v,S_p,J_j$ with its own prescribed $d_A$, without substituting a different open-extension comparison.

Original cited nodes: lem-sf-generator-reduction-coherence, lem-coef-derived-system-evaluation-calculus

### Original step 5

For two smaller trees write $M=M_V$, $N=M_T$ and use their independent input slots. Transposing their binary coefficient composite gives
$$b_{V\otimes T}=\mathcal L(q_V\otimes^Lq_T)d_\otimes(I_V,I_T)^{-1}.$$
Substitute $q_V=e_M\mathcal R(b_V)$ and $q_T=e_N\mathcal R(b_T)$. Bifunctoriality factors their tensor into $(e_M\otimes^Le_N)(\mathcal R(b_V)\otimes^L\mathcal R(b_T))$. Naturality of the two-input $d_\otimes$ then gives
$$b_{V\otimes T}=\mathcal L(e_M\otimes^Le_N)d_\otimes(\mathcal LM,\mathcal LN)^{-1}(b_V\widehat\otimes^Lb_T).$$
Every factor is invertible; in particular tensor sends the inverses of $e_M,e_N$ to the inverse of their tensor. Invert this identity to get
$$b_{V\otimes T}^{-1}=(b_V^{-1}\widehat\otimes^Lb_T^{-1})d_\otimes(\mathcal LM,\mathcal LN)\bigl(\mathcal L(e_M\otimes^Le_N)\bigr)^{-1}.$$
This is precisely the claimed tensor recursion with $a_\otimes(M,N)$. All tensors in the system calculation are over the ring system $((A_n)_W)_n$; the tensor on integral objects is the completed tensor specified by $d_\otimes$.

Original cited nodes: lem-sf-generator-reduction-coherence, lem-coef-derived-system-evaluation-calculus

### Original step 6

Induct on the number of operation vertices in the finite well-typed tree. The variable case is step 3, the unary step is step 4, and the binary step is step 5; both immediate subtrees have fewer vertices. These steps construct invertible $b_V$ on exactly the assumed domains. The canonical reduction/limit transport is $c_V=b_V^{-1}$: step 3 starts with the identity comparison of the reduction of a variable, substitutes the prescribed basic coefficient maps, and takes their adjunction transpose. This also agrees directly with the specified construction in [lem-sf-integral-compactification-system-realization]: inserting $e_M^{-1}:M\to\mathcal R\mathcal LM$ before a basic $d_A$ gives exactly the last two factors of step 4, and inserting $e_M^{-1}\otimes^Le_N^{-1}$ gives those of step 5. Thus the calculation identifies the specified comparisons themselves. It does not infer their normalization merely from the existence or generator-intertwining assertion of that node. Finally any other family satisfying the displayed identities equals this one: equality holds at variables, and at a unary or tensor node the fixed $a_A$ or $a_\otimes$ and the induction equalities of the children give equality at that node. This proves the characterization without moving any clause into a new lemma.

Original cited nodes: lem-sf-integral-compactification-system-realization, lem-sf-generator-reduction-coherence, lem-coef-derived-system-evaluation-calculus

### Original step 7

The recursion is natural on the specified input domains. For a system map $f:M\to M'$, counit naturality says $f e_M=e_{M'}\mathcal R\mathcal L(f)$. Apply $\mathcal LA$ and solve for the inverse factors to get
$$\bigl(\mathcal LA(e_{M'})\bigr)^{-1}\mathcal LA(f)=\mathcal LA\mathcal R\mathcal L(f)\bigl(\mathcal LA(e_M)\bigr)^{-1}.$$
Naturality of $d_A$ now yields $a_A(M')\mathcal LA(f)=A_{\rm int}(\mathcal Lf)a_A(M)$. For maps $f:M\to M'$ and $g:N\to N'$, tensor the two counit equations and apply the same calculation with the two-input $d_\otimes$; it yields
$$a_\otimes(M',N')\mathcal L(f\otimes^Lg)=(\mathcal Lf\widehat\otimes^L\mathcal Lg)a_\otimes(M,N).$$
The inverse-unit leaf comparison is natural because $u$ is natural. Paste these unary and binary squares with the induction squares for the children. This proves naturality of every $c_V$ in all independent leaf slots. A zero input and an empty open give the unique maps on zero objects; a single leaf gives the actual inverse unit, rather than an arbitrary automorphism of its limit. At a point with $K=R[0]$, a one-operation expression specializes to its specified $d_A$ by the triangle calculation in step 3. No level $n=0$ or shift compatibility is used.

Original cited nodes: lem-coef-derived-system-evaluation-calculus, lem-sf-generator-reduction-coherence

## Unfinished work

No Lean is written or compiled. The two extracted nodes intentionally remain statement-only for independent stage-1 work. Delivery validation follows below.
