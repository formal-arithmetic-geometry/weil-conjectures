# Worker report

1. Files written: `dag/nodes/sec-poincare-duality/lem-pod-semilinear-field-operation-lifts.json` (statement unchanged; seven-step assembly, 2627 characters); `lem-pod-isomorphism-field-transport.json` (statement, unsplit, no Mathlib match); `lem-pod-frobenius-pullback-ordinary-exchange.json` (statement, unsplit, no Mathlib match). Both new nodes have empty proof, empty proof_deps and null proof_origin. `citations.json` supplies a literal statement quotation for every parent citation. Search results are recorded in `searches.jsonl` by the required msearch command.

2. Attachments: none. I searched the actual library under `lean/WeilConjectures/` for the item tag and notion, then read WeilComplexInternalHom and the relevant generic lift declarations. Those implement finite-coefficient etale/finite-Tor fixed pairs, not all the completed, raw rational and common-stage clauses of this item. The recorded Sheaf.Paper.SemilinearFieldOperationLifts declarations are also not an attachment: I read their statements and found sorry in the actual field-pullback and supplied-operation theorems. No Lean was changed or compiled.

3. WANTED: none. The blueprint sources needed are present; the omitted coefficient and mate arguments are agent-formulated and remain marked as such in the parent proof_origin. No SGA source was used.

4. This is the dedicated repair in coord/returns/Q23.md and coord/repair-notes/lem-pod-semilinear-field-operation-lifts.json (batch5, 2026-10-22). Its point is to distribute the existing 8500-character proof rather than summarize it away. I therefore preserve the exact statement, provide two substantial independently claimable children and retain the elementary computations in the parent. No target, definition or coefficient category was changed. The chapter and unit records remain untouched; this is not the unit's key statement.

5. Unfinished work: the two children are deliberately statement-only. Their independent workers must prove the original arguments allocated below. The parent is a complete assembly conditional on those named results; it does not claim that any sorried Lean has been proved.

## Repair allocation

The first child carries original Steps 2 and 3, including the actual completed coefficient identification, the lambda-defined inverse identities, exact termwise transport, raw localized Hom maps, all common-field arrow conjugations and the mixed scalar equation needed for naturality of the inverse identity. It generalizes Frobenius to any scheme isomorphism between finite-type k-schemes, with no separatedness or k-linearity assumption. Its equation is the literal inverse-identity normalization of lem-pod-pullback-identities-scalar-extension (2).

The second child carries original Step 4 and the ordinary-direct-image part of Step 5. It treats any commuting pair of scheme automorphisms over a separated finite-type k-morphism: the canonical composition-normalized square, its finite reductions, the two composite scalar comparisons and their explicit intertwining equation, rational/common-stage descent and the specified ordinary mate. It supplies underlying comparison maps only, before any Weil data. Compact-support exchange remains an existing node, not a new restatement. Neither child alone restates the item or supplies its Weil lifts; the parent still proves the arrow equations for all five operations.

Original Step 1 is parent Step 1. Original Steps 2–3 are invoked in parent Step 2. Original Step 4 and ordinary part of Step 5 are invoked in parent Step 3, which also retains the original compact-support citation. Original Steps 6, 7 and 8 are parent Steps 4, 5 and 6, with each displayed arrow calculation still present. Original Step 9 is parent Step 7. The original full prose is reproduced below for the future child workers and the independent maintainer reader. It is not hidden inside either child's statement as a proof sketch.

## Not duplicates

lem-pod-isomorphism-field-transport vs lem-sf-automorphism-constructible-stage-equivalence: the latter assumes T separated over k and treats an automorphism of T; the new node covers isomorphisms between arbitrary finite-type k-schemes including non-separated ones, and pins the lambda-defined inverse identity and its common-field conjugation equation. It does not use a separated-scheme theorem on a non-separated scheme.
lem-pod-isomorphism-field-transport vs lem-weil-isomorphism-derived-pullback: the existing node supplies the integral/finite lambda and constructibility only; the child proves inverse equivalences and their normalized raw rational/common-stage descent.
lem-pod-isomorphism-field-transport vs lem-pod-pullback-identities-scalar-extension: the existing node supplies the mixed scalar identities, not the construction and exactness of the coefficient-stage equivalences.
lem-pod-frobenius-pullback-ordinary-exchange vs lem-pod-integral-pullback-composition: the latter gives integral composition only, not the commuting-square field comparison, common-field descent or its ordinary mate.
lem-pod-frobenius-pullback-ordinary-exchange vs lem-weil-mate-iso-along-equivalences: the latter is an abstract criterion, not the geometric coefficient normalization or identification with the prescribed exchange.
lem-pod-frobenius-pullback-ordinary-exchange vs lem-pod-constructible-mate-coherence: that node assumes standard lifts and studies exceptional adjoints and equivariance, whereas this child constructs the underlying pullback and ordinary comparison without Weil structures or an exceptional adjoint.
Both children vs lem-fix-weil-operations: this blueprint ancestor states the larger Weil-operation package and depends on the present item; citing it would be circular. It is the source route being refined, not an independent smaller input.

I searched the whole DAG for the prospective ids, isomorphism/equivalence/scalar/common-stage statements, and square/mate comparisons, and used blueprint_refs.py ancestor/search (semilinear, pullback composition, scalar localization, equivariant, bifunctor, fixed pairs, isomorphism, pullback square). No equal statement appeared. Relevant existing nodes were read and distinguished above. No new node carries a Stacks tag shared with an existing node: both source records point to the exact blueprint sentence whose omitted arguments they isolate. Underlying tagged results remain the existing nodes.

## Mathlib search review

For the first child I ran two semantic phrasings, LeanSearch, Loogle and grep using its exact intended statement. The hits are ordinary sheaf/module pullbacks, site equivalences and exact-functor derived localization. I read Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:189,241,265, the Endofunctor/Algebra functorOfNatTrans at line 156, and the exact-functor derived-category factorization. None constructs the completed coefficient isomorphism together with normalized inverse identities through raw scalar and common-stage field categories.

For the second child I ran two semantic phrasings, LeanSearch, Loogle and a targeted grep. Modules/Sheaf.lean:241 and :265 are the ordinary module compositor and its conjugate, with different coefficient sheaves and no completed or common-stage descent. The Loogle pullbackComparison hits are categorical limit cones, not the specified derived operation square. No hit is a one-line specialization of the child. I also searched generic fixed-pair multifunctor lifts; these returned localization lifting and internal-Hom bifunctors, so I retained the elementary explicit arrow arguments rather than manufacturing a new generic lemma. Every search listed in either child is an actual command recorded in searches.jsonl; all selected services answered successfully. Older searches on the item are preserved, not claimed as searches made by Q23.

## Review by Q23

I read coord/delivery-errors.md B–E in both copies, the worker brief, stage-1 contract, GOAL.md, the three-level route policy, chapter and unit, and the dedicated repair entry. I read the source prop-weil-operations.proof.md sentence 1 and the entire first paragraph of main-20261015 lem-fix-weil-operations.proof.md: it specifies Ex_* then pushforward of theta, Ex_!, commuting pullbacks, tensor, and the inverse first-variable Hom datum. Those are exactly the steps retained here. For each child I read the same source with its assigned original Steps 2–3 or 4–5, and the existing input statements described below. These are two arguments of comparable scope, not elementary nodes or two restated conclusions. The parent has no non-elementary step longer than 2000 characters and its total proof text is below 3000.

Parent Step 1 uses lem-weil-frobenius-square-cartesian clauses 1–3 verbatim: it gives scheme isomorphisms, the commuting equation and Cartesian property. I checked the restructured k-map equation a_Y g_Y f = a_X g_X using that equation and a_Y f = a_X, without calling geometric Frobenius a k-map.

Parent Step 2 uses the first child's full integral, rational and common-stage inverse-equivalence conclusion. The item has finite-type k-schemes and ell invertible because ell differs from p; neither separatedness nor k-linearity is required. For the child's future proof I checked the exact inverse-image and limit statements in lem-weil-proetale-isomorphism-inverse-image, natural constructibility-preserving lambda in lem-weil-isomorphism-derived-pullback, raw localized Homs and triangle convention in def-weil-rationalization-karoubi, actual common-field Homs and triangles in def-weil-algebraically-closed-coefficients, and the tower-normalized alpha and inverse-identity equation in lem-pur-integral-operations-scalar-extension and lem-pod-pullback-identities-scalar-extension (2). That last compatibility is indispensable; componentwise inverse identities alone do not prove common-stage naturality.

Parent Step 3 applies the second child with the two Frobenius automorphisms of Step 1 and uses lem-pod-weil-frobenius-compact-support-exchange for Ex_!; that node explicitly allows non-separated bases and both field stages, with preserved finite-Tor domains. For the second child's future proof I checked the direction c_(f,gY) c_(gX,f)^(-1), the finite reductions from lem-pod-integral-pullback-composition and lem-weil-pbc-proetale-derived-pullback-composition, and the scalar compatibility in lem-pod-pullback-identities-scalar-extension (1). The composites A and B in the child have respectively sources T_X(P_X Lf* K) and T_X(Lf* P_Y K), so B T(a) = a_L A is well typed. The mate uses ordinary Lf* adjoint Rf_* from fix-prop-adjunctions (1); lem-weil-mate-iso-along-equivalences applies with G=P_Y an equivalence and G'=P_X fully faithful. The unit-comparison-counit formula agrees exactly with def-exchange-projection, read with its supplied higher-coefficient data, not with an implicit existence assertion. This is why the item still retains all prescribed constructibility domains.

Parent Step 4 uses def-weil-weil-sheaf-complex's arrow condition and literal underlying identities/composition. It proves the covariant arrow equation by functoriality and naturality, with both structure factors invertible. Parent Step 5 uses lem-pur-derived-pullback-tensor-iso's actual natural mu at the field stages and the tensor bifunctor of def-weil-derived-pullback-tensor-hom. Both input arrow equations are substituted explicitly. Parent Step 6 uses lem-pod-derived-automorphism-hom-evaluation's natural isomorphism for arbitrary scheme isomorphisms on constructible internal-Hom pairs, not a site-perfectness assertion. The inverse first structure has type M to PM, and the equation theta_M^(-1) u = Pu theta_Mprime^(-1) has matching domains. Def-weil-derived-pullback-tensor-hom supplies precisely the contravariant/covariant composition law written out. Parent Step 7 uses only the definition's forgetful functor and makes no enlarged domain or triangulated-pair claim. citations.json quotes the actual statement of every input, including both new children; no source proof is masquerading as a statement citation.

Small cases checked: empty schemes/zero objects give the zero transport and maps; g=id and E=L give the specified identity comparisons; f=id gives the ordinary identity-square mate. On the geometric point, rank-one Frobenius scalars x,y give xy for tensor and y/x for Hom, so the inverse in the first variable is necessary. Non-separated finite-type examples are allowed because neither child assumes separatedness of the base; only f is separated. Arbitrary localized arrows (and scalars such as ell^(-1)) are handled by linear extension and the specified common-stage conjugations, never by choosing an invariant integral lattice. The two inverse identities are natural isomorphisms; no assertion that unrelated choices of lambda are normalized was made.

I corrected no mathematical statement. I made the second child apply to arbitrary commuting scheme automorphisms so it is a reusable comparison result before Weil structures, and explicitly introduced the integral coefficient ring, uniformizer and quotient rings in the first child. All existing metadata and searches on the item are preserved. The earlier local dependency inspection found a pre-existing cycle deep in unrelated ring-hom extension nodes; it is not a new dependency back to this item, and the required server checks judge the overlay. No unrelated node was changed.

## Original arguments allocated to the new workers

### Original Step 1

By [lem-weil-frobenius-square-cartesian], $g_X,g_Y$ are scheme isomorphisms, $fg_X=g_Yf$, and the displayed square is Cartesian. This does not assert $k$-linearity. Indeed, if $a_T:T\to\operatorname{Spec}k$ is the usual structure map, the upper copy of $T$ has structure map $a_Tg_T$; then $g_T$ is a map to the lower copy over $k$, and $a_Yg_Yf=a_Xg_X$ makes the left vertical arrow a map over $k$. These are precisely the restructured source corners in the assertion.

Inputs: lem-weil-frobenius-square-cartesian

### Original Step 2

For each $T$, [lem-weil-proetale-isomorphism-inverse-image] gives the exact inverse-image equivalence on module sheaves, its inverse, and its compatibility with the completed coefficient sheaf (inverse image commutes with the inverse limit of constant coefficient sheaves). [lem-weil-isomorphism-derived-pullback] identifies the completed constructible pullback with this termwise transport, $\lambda^{g_T}_K:P_TK\xrightarrow{\sim}g_T^{-1}K$, and asserts that it preserves $D^b_c$. Apply the same result to $\bar g_T=g_T^{-1}$. Put $\epsilon_K:L\bar g_T^*P_TK\xrightarrow{\sim}K$ equal to $\lambda^{\bar g_T}_{P_TK}$, followed by $\bar g_T^{-1}(\lambda^{g_T}_K)$ and the canonical isomorphism of inverse images along $g_T\circ\bar g_T=\mathrm{id}$; define the other composite symmetrically with $g_T$ and $\bar g_T$ exchanged. These are natural isomorphisms, since $\lambda$ is natural and the inverse images are inverse site equivalences, so the two pullbacks are inverse equivalences on the integral constructible categories. Exactness follows already on module sheaves, hence also after passage to complexes and quasi-isomorphisms.

Inputs: lem-weil-proetale-isomorphism-inverse-image, lem-weil-isomorphism-derived-pullback

### Original Step 3

At $E$, use the raw scalar localization of [def-weil-rationalization-karoubi]: the integral functors $P_T$ and $L\bar g_T^*$ act on $\operatorname{Hom}(-,-)\otimes_{\mathcal O_E}E$ by $u\otimes c\mapsto P_T(u)\otimes c$, so the inverse-identity isomorphisms of Step 2 stay natural for every $u\otimes c$ by linearity and each inverse identity remains the same equality after tensoring. At $\overline{\mathbf Q}_\ell$, [def-weil-algebraically-closed-coefficients] represents every object and arrow over a common finite field, and the pullbacks act on an arrow represented over $L$ by its stage-$L$ image conjugated by the rationalized pullback scalar-extension comparisons $\alpha$ of [lem-pur-integral-operations-scalar-extension]; these are natural, unital and compatible with successive extension, so the action does not depend on the representative. At $(E,K)$ take the class of the stage-$E$ isomorphism $\epsilon_K$ of Step 2. By [lem-pod-pullback-identities-scalar-extension] (2), the scalar extension of $\epsilon^E_K$ is $\epsilon^L$ at the extended object composed with exactly the two comparisons $\alpha$ by which the composite functor $L\bar g_T^*P_T$ acts on arrows over $L$. Hence for an arrow represented over $L$ the naturality square of these classes is the stage-$L$ naturality square of $\epsilon^L$ conjugated by those comparisons, and so commutes; tower compatibility makes the class independent of the representing field. Applying the same clause to $\bar g_T$ gives the other inverse identity. These identities therefore hold in the common-stage category too. This also preserves the exact structures, whose triangles are images of integral triangles or are represented over a common finite field.

Inputs: def-weil-rationalization-karoubi, def-weil-algebraically-closed-coefficients, lem-pur-integral-operations-scalar-extension, lem-pod-pullback-identities-scalar-extension

### Original Step 4

For $F=Lf^*$, form $a:P_XLf^*\xrightarrow{\sim}Lf^*P_Y$ as $c_{f,g_Y}\circ c_{g_X,f}^{-1}$ through $L(fg_X)^*=L(g_Yf)^*$, where $c_{h,k}:L(kh)^*\xrightarrow{\sim}Lh^*Lk^*$. At the integral stage these are the natural isomorphisms $c^{\mathcal O_E}_{h,k}$ of [lem-pod-integral-pullback-composition], which apply to arbitrary morphisms of schemes on which $\ell$ is invertible and whose reductions modulo $\varpi_E^n$ are the finite composition isomorphisms of [lem-weil-pbc-proetale-derived-pullback-composition]; thus $a^{-1}$ is the square identification $\theta$ from which [def-exchange-projection] builds $\operatorname{Ex}_*$. At $E$, $a\otimes1$ is natural for every $u\otimes c$ by linearity. At $\overline{\mathbf Q}_\ell$ take at $(E,K)$ the class of the stage-$E$ component. By [lem-pod-pullback-identities-scalar-extension] (1), applied to the pairs $(g_X,f)$ and $(f,g_Y)$, the scalar extension of $c^{\mathcal O_E}$ is $c^{\mathcal O_L}$ conjugated by the composite comparisons $\alpha$ of [lem-pur-integral-operations-scalar-extension], which are exactly the comparisons by which $P_XLf^*$ and $Lf^*P_Y$ act on arrows over $L$. So the classes are natural for arrows represented over any common field and independent of the representing field. Hence $a$ is a natural isomorphism of the specified pullbacks at both field stages.

Inputs: lem-pod-integral-pullback-composition, lem-weil-pbc-proetale-derived-pullback-composition, def-exchange-projection, lem-pur-integral-operations-scalar-extension, lem-pod-pullback-identities-scalar-extension

### Original Step 5

For $F=Rf_*$ use $Lf^*\dashv Rf_*$ from [fix-prop-adjunctions] (1). With $L=L'=Lf^*$, $R=R'=Rf_*$, $G=P_Y$, $G'=P_X$, the inverse of the comparison in Step 4 has type $L'G\xrightarrow{\sim}G'L$. Its mate is exactly $\operatorname{Ex}_*$ in [def-exchange-projection], since that definition is the unit--pullback-comparison--counit composite. By [lem-weil-mate-iso-along-equivalences] it is invertible: Step 3 gives that $G$ is an equivalence and $G'$ is fully faithful. For $F=Rf_!$, [lem-pod-weil-frobenius-compact-support-exchange] gives the canonical natural isomorphism $\operatorname{Ex}_!$ at both field stages on the stated domains, without separatedness of either base scheme. Thus all three covariant comparisons $a$ are natural isomorphisms.

Inputs: fix-prop-adjunctions, def-exchange-projection, lem-weil-mate-iso-along-equivalences, lem-pod-weil-frobenius-compact-support-exchange

### Original Step 6

Let $F$ be any of the three functors with its comparison $a$, and set $\Theta_K=F(\theta_K)a_K$. Both factors are invertible. If $u\theta_K=\theta_LP_{\mathrm{in}}(u)$, functoriality and naturality give
$$F(u)\Theta_K=F(u\theta_K)a_K=F(\theta_L)F(P_{\mathrm{in}}u)a_K=F(\theta_L)a_LP_{\mathrm{out}}(F(u)).$$
This is exactly the arrow condition in [def-weil-weil-sheaf-complex]. Identities and composition are preserved because the underlying arrows are $F(u)$; equality of arrows of pairs is equality of underlying arrows. Hence this gives the asserted three functors, including the specified direct-image formulas.

Inputs: def-weil-weil-sheaf-complex

### Original Step 7

For tensor use the natural isomorphism $\mu_g$ of [lem-pur-derived-pullback-tensor-iso] at the field stages and put $\Theta_{M,N}=(\theta_M\otimes\theta_N)\mu_{M,N}$. It is invertible. For Weil arrows $u:M\to M'$ and $v:N\to N'$, bifunctoriality, their two arrow equations, and naturality of $\mu$ give
$$(u\otimes v)\Theta_{M,N}=(u\theta_M\otimes v\theta_N)\mu_{M,N}=(\theta_{M'}\otimes\theta_{N'})(P_Wu\otimes P_Wv)\mu_{M,N}=\Theta_{M',N'}P_W(u\otimes v).$$
Tensor preserves identities and simultaneous composition, so the same holds for its lift. This calculation uses only the natural tensor comparison and its defining bifunctor; it makes no additional preservation assertion.

Inputs: lem-pur-derived-pullback-tensor-iso, def-weil-derived-pullback-tensor-hom

### Original Step 8

Write $H=R\mathcal Hom$. [lem-pod-derived-automorphism-hom-evaluation] supplies the canonical natural isomorphism $h_{M,N}:P_WH(M,N)\xrightarrow{\sim}H(P_WM,P_WN)$ for an arbitrary scheme isomorphism, with the completed integral realization and its localized/common-stage forms, on pairs whose internal Hom is constructible. Set $\Theta_{M,N}=H(\theta_M^{-1},\theta_N)h_{M,N}$, an isomorphism. For arrows $u:M'\to M$, $v:N\to N'$ of Weil pairs, their equations imply $\theta_M^{-1}u=(P_Wu)\theta_{M'}^{-1}$ and $v\theta_N=\theta_{N'}P_Wv$. Contravariant/covariant functoriality and naturality of $h$ give
$$H(u,v)\Theta_{M,N}=H(\theta_M^{-1}u,v\theta_N)h_{M,N}=H(\theta_{M'}^{-1},\theta_{N'})H(P_Wu,P_Wv)h_{M,N}=\Theta_{M',N'}P_W(H(u,v)).$$
Thus $H(u,v)$ is a Weil arrow. Its identity and composition laws are the laws of the internal-Hom bifunctor in [def-weil-derived-pullback-tensor-hom]. The inverse in the first input is essential: it has type $M\to P_WM$, precisely the contravariant input required for a map $H(P_WM,P_WN)\to H(M,N)$.

Inputs: lem-pod-derived-automorphism-hom-evaluation, def-weil-derived-pullback-tensor-hom

### Original Step 9

All constructions above leave each underlying object and arrow equal to the value of the stipulated operation. The forgetful functor of [def-weil-weil-sheaf-complex] therefore recovers all five operations. We have restricted throughout to the existing preserved constructible domains; tensor and Hom keep the finite-Tor and any site-perfect first-variable restrictions stated in the item. The formulas introduce no change to any underlying derived functor, shift comparison or underlying triangle. Thus their exactness means exactly the exactness already available for those underlying derived functors (in each covariant variable, and contravariantly in the first Hom variable); it supplies no triangulated-category claim about the category of pairs.

Inputs: def-weil-weil-sheaf-complex

