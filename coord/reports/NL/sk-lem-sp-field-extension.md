# NL stage-1 dedicated repair report

## Files written

sk-lem-sp-field-extension.json: statement unchanged byte for byte; replaced the 10278-character proof by three assembly steps.

lem-pur-integral-coefficient-model-comparison: statement-only, unsplit; searched by LeanFinder, LeanSearch, Loogle and source grep, no exact or one-line Mathlib match.

lem-pur-purity-conjugated-coefficient-adjunction: statement-only, unsplit; searched by LeanFinder, LeanSearch, Loogle and source grep, no exact or one-line Mathlib match.

lem-pur-rationalized-smooth-adjunction-diagrams: statement-only, unsplit; searched by LeanFinder, LeanSearch, Loogle and source grep, no exact or one-line Mathlib match.

dag/units/sk-lem-sp-field-extension.json: only realized and realized_by populated; chapter, unit statement and route unchanged. citations.json quotes every statement used by each parent step. searches.jsonl preserves actual search results.

## Attachments

None. Searched the live WeilConjectures sources for the exact blueprint tag, purity, coefficient extension and localized-adjunction notions. No project declaration proves the whole item or a whole new prerequisite with these normalized comparison data. Generic category-theory declarations do not attach a geometric coefficient theorem.

## Literature wanted

WANTED: none. The proof is agent-written, as was its inherited blueprint proof. Source passages read: main-20261015/sk-lem-sp-field-extension/_section.md and sk-lem-sp-field-extension.proof.md; sk-lem-sp-field-extension-towers.md and its proof in the same directory; sk-prop-sp-rational/sk-prop-sp-rational.proof.md. The new statements extract the expanded arguments already present in the reviewed live DAG; they are not represented as verbatim theorems from Stacks. The strict-tower limit prerequisite itself cites Stacks 0940/0941 (sites-cohomology.tex, section-derived-limits / lemma-derived-limit-is-ok). No SGA route is used.

## Return repaired

Read the dedicated handoff in coord/returns/NL.md, head 4337f138bbc9c47d80458b78fc0391322e56aeed. The initial dry run confirmed the re-split gate: unchanged node, proof >3000 characters, fewer than three new nodes. This repair supplies exactly three new independent statement-only tasks and a parent assembly below 3000 characters. Nothing has been erased to meet a length limit. The allocation below and the preserved old proof give the future worker the whole argument. The parent statement and all imported blueprint metadata remain unchanged.

## Argument allocation

1. Integral coefficient model comparison carries old Step 2 in full: tensor-to-completed chi transport, naturality, both unit/counit equations, alternative G adjoint, counit-preserving theta and its unit identity by transposition, transport back to J, and cancellation of intermediate theta factors in coefficient composition. It also carries the completed associator formula and its identification in old Step 6. This is before rationalization.
2. Purity-conjugated coefficient adjunction carries old Step 1 (transported adjunction and triangle identities), old Step 3 (the two explicit gamma unit/counit calculations), and the gamma-cancellation cocycle and identity-extension part of old Step 6. It assumes integral comparisons; it does not construct coefficient change on schemes.
3. Rationalized smooth adjunction diagrams carries old Step 4 (localization, inverses, pure-tensor and finite-sum naturality), old Step 5 (linearity via the strict tower lift and K-injective termwise limit, linearity of inverse transposition, tensoring the bijection and localizing units/counits), and the last localization of the cocycles in old Step 6. It assumes integral comparisons rather than asserting their existence.

## Not duplicates

lem-pur-integral-coefficient-model-comparison vs det-sp-field-extension-towers: the existing theorem supplies comparisons for ordinary derived tensor, and the new task specifies the chi-conjugated completed maps, alternative exceptional-adjoint model normalization and completed associator used in rationalization; it does not repeat the finite-tower construction.

lem-pur-integral-coefficient-model-comparison vs lem-weil-finite-free-completed-scalar-comparison: the latter provides chi and derived completeness, not the compact-support/right-adjoint diagram or its units, counits and coefficient cocycles.

lem-pur-purity-conjugated-coefficient-adjunction vs lem-weil-pbc-mate-pasting: mate pasting gives composition of conjugate squares; the new task specifies simultaneous replacement of right adjoints by gamma, the induced adjunctions, both diagram equations and their coefficient-indexed cocycle, without requiring a conjugate transformation as an input.

lem-pur-purity-conjugated-coefficient-adjunction vs lem-pur-adjoint-equivalence-conjugation-calculus: that theorem conjugates entire categories through adjoint equivalences with invertible units/counits; here categories and left functors stay fixed and only right functors are replaced; the original adjunction units/counits need not be invertible.

lem-pur-purity-conjugated-coefficient-adjunction vs lem-sfb-adjunction-transport-left-iso: the old lemma changes a left adjoint and supplies a Hom bijection, with no coefficient diagrams or cocycles; this task changes right adjoints and proves the simultaneous coefficient coherence.

lem-pur-rationalized-smooth-adjunction-diagrams vs lem-pur-transport-rational-hom-counit: that theorem uses intrinsic condensed finite-Tor categories, trace/purity families and coefficient comparisons from this item, so citing it would be circular; this node proves linearity and raw scalar-localization diagrams directly in the derived-complete/raw localized categories.

lem-pur-rationalized-smooth-adjunction-diagrams vs lem-sfb-adjunction-localization: the latter assumes general categorical localizations and supplied descended functors; it does not supply strict-tower compact-support linearity or the explicit raw tensor-Hom and coefficient-diagram normalization here.

lem-pur-rationalized-smooth-adjunction-diagrams vs lem-sf-rational-direct-image-adjunctions: that theorem concerns a right adjoint of rational inverse image and invertible scalar-change mates; here compact-support direct image is the left adjoint and twisted pullback the right adjoint, constructed from the integral tower and scalar Hom localization.

The whole DAG was searched by finite-extension, linear-adjunction, localization, conjugation and model-transport notions, including statement-only scans, not merely node names. The whole blueprint was searched with blueprint_refs.py for finite extensions, scalar localization, conjugation, right adjoint and transport adjunction. None states one of the extracted normalized interfaces exactly. Exact project tag search and concept searches found only partial/different operations. New ids were checked absent before writing.

## Review by NL

I read the item statement against the current blueprint unit and sole proof paragraph, including its tower and rational-adjunction supporting paragraphs. The existing correction interpreting rational tensor as raw localization of completed integral scalar extension is preserved. The standing finite-field, separated finite-type and ell-invertible hypotheses are explicit; I have not replaced the lecture-notes purity route.

Parent Step 1 uses det-sp-field-extension-towers only for clauses (1)-(2): preservation of derived-complete constructibles and actual tower-derived tensor comparisons. I opened its statement: it names J=H and explicitly gives both adjunction and composition compatibilities. The new integral-model node supplies exactly the displayed completed b0,c0, unit/counit equations and associator cocycles; it does not infer equality of integral morphisms from equality after reduction. The optional alternative G clause assumes a specified constructible adjunction and supplied unit/counit-compatible comparison, then proves its transport. It is never assumed for an arbitrary ambient right adjoint.

Parent Step 2 uses det-sp-integral-adjunction-bijection for the integral adjunction and actual gamma isomorphism, and the new conjugation lemma for precisely the etaH, epsilonH, a0 formulas and their two diagram equations. All four corners and composition directions were checked. In the unit equation naturality moves gammaF inverse across JF(b0); in the counit equation PF(gammaF) cancels PF(gammaF inverse) and naturality moves b0 across gammaE. The middle gamma factors cancel in the three-index cocycle; the associators are restored at the endpoints, rather than suppressed permanently. This is a separate diagram-coherence task, not a new assertion of rational field-extension compatibility.

Parent Step 3 uses only the rationalized-diagrams node, whose statement includes the geometric integral linearity, tensor-Hom adjunction normalization, inverses and finite-sum naturality, both rationalized unit/counit equations, and the rationalization of integral cocycles. It assumes the comparisons already supplied by Steps 1-2. In its source argument the strict compact-support lift is linear and derived limit is computed on K-injective tower resolutions: scalar multiplication and addition on maps survive termwise limit. The inverse transpose epsilonH composed with P(v) is linear, hence so is the bijection inverse. Tensoring a linear isomorphism preserves its inverse without any claim about an arbitrary chosen lift. The localized objects are literally the same objects; every arrow is a finite sum of pure tensors, so naturality on those tensors proves the whole square. These claims are in the new statement rather than hidden in the short parent assembly.

For each new node I checked B1-B10: no proof steps or proof dependencies; independent complete hypotheses and objects; sources and exact blueprint proof places; notions cite definitions; single TeX escaping; logged search results are recorded exactly with actual availability; none is an exact Mathlib specialization. Read Mathlib Adjunction/Basic.lean (ofNatIsoRight and homEquiv formulas), Adjunction/Unique.lean (rightAdjointUniq and unit/counit identities), Adjunction/Mates.lean (mateEquiv_counit and unit_mateEquiv), Localization/Adjunction.lean (localization and unit/counit formulas), and AlgebraicGeometry/Sites/ElladicCohomology.lean (definitions only). The generic transport declarations cover pieces, not the new full normalized interfaces. New statements are statements only; the inherited calculations below are proof guidance in this report.

Small cases: E=F, F=L, ramified finite coefficient extensions (the input is finite free, not unramified), d=0, empty source/target, zero objects and zero morphisms. The model transport uses natural isomorphisms and triangle identities only, so none needs nonempty categories or nonzero Hom groups. In the identity coefficient case the cocycle is an invertible idempotent and hence the identity under unitors. No unproved faithfulness or conservative reduction is used. No target or statement dispute was needed.

Long-step review: all parent steps are under 2000 characters. The old long Steps 2 and 6 contained the model and associator arguments now assigned explicitly above, rather than being silently compressed. The initial dry-run failures are repaired by the actual new task boundaries, not just a shorter parent text.

## Preserved inherited proof guidance

The following is the complete previous six-step argument, preserved for workers of the extracted tasks. It is guidance in the report, not a proof attached to an unsplit node.

### Original step 1

Put $P_R=Rf_{!,\mathcal O_R}$, $J_R=H_{f,\mathcal O_R}$ and $H_R=Lf_{\mathcal O_R}^*(-)(d)[2d]$ for a coefficient field $R$. The integral adjunction statement gives $P_R\dashv J_R$ and a natural purity isomorphism $\gamma_R:H_R\xrightarrow{\sim}J_R$. Transport this adjunction to $P_R\dashv H_R$: explicitly $\eta_R^H=\gamma_{R,P_R(-)}^{-1}\eta_R^J$ and $\epsilon_R^H=\epsilon_R^J P_R(\gamma_R)$. The triangle identities follow by substituting these formulas, using naturality of $\gamma_R$, and cancelling $\gamma_R^{-1}\gamma_R$. These are exactly the integral data used in the blueprint's rational adjunction.

Uses: det-sp-integral-adjunction-bijection

### Original step 2

For $E\subset F$ write $C_T$ for the strict inverse-limit integral coefficient extension underlying the statement's rational functor. The tensor extension in [det-sp-field-extension-towers] is initially $T_T(-)=(-)\otimes^L_{\widehat{\mathcal O}_{E,T}}\widehat{\mathcal O}_{F,T}$. By [lem-weil-finite-free-completed-scalar-comparison] there is a specified natural isomorphism $\chi_T:T_T\xrightarrow{\sim}C_T$ on derived-complete inputs. All inputs here, including $P_EM$ and the exceptional images, are in those categories by the cited integral adjunctions. Transport the tensor-version comparisons $b^t,\widetilde c^t$ to $C$ by
$$
 b^0_M=P_F(\chi_{X,M})\circ b^t_M\circ\chi_{Y,P_EM}^{-1},
 \qquad
 \widetilde c^0_K=G_F(\chi_{Y,K})\circ\widetilde c^t_K\circ\chi_{X,G_EK}^{-1}.
$$
Naturality follows by substitution and naturality of $\chi$. In the unit and counit equations the inserted $\chi^{-1}\chi$ factors cancel, using naturality to move them across the integral units and counits. Composition compatibility is transported with the scalar-extension associators, rather than identifying the two integral functors by definition. Clauses (1)-(2) of the integral field-extension theorem give natural isomorphisms $b^0:C_YP_E\to P_FC_X$ and $\widetilde c^0:C_XG_E\to G_FC_Y$, with unit, counit and composition compatibility, where $G_R$ denotes its integral exceptional right adjoint. Its finite-level maps form actual maps of towers before taking $R\varprojlim$; no equality of integral morphisms is inferred merely from equality of their reductions. If this is already the normalized tower model $J_R$, set $\theta_R=1$. For the project's exceptional model use the constructible adjunction in the integral exceptional-adjoint theorem and right-adjoint uniqueness to obtain the counit-preserving isomorphism $\theta_R:J_R\to G_R$. Thus
$$\epsilon_R^G\circ P_R(\theta_R)=\epsilon_R^J,\qquad \theta_{R,P_RM}\circ\eta_R^J(M)=\eta_R^G(M).$$
For the second equality, the $G_R$-transpose of its left side is $\epsilon_R^G(P_RM)P_R(\theta_{R,P_RM})P_R(\eta_R^J(M))=\epsilon_R^J(P_RM)P_R(\eta_R^J(M))=1_{P_RM}$, which is also the transpose of $\eta_R^G(M)$. Define
$$c^0_K=\theta_{F,C_YK}^{-1}\circ\widetilde c^0_K\circ C_X(\theta_{E,K}):C_XJ_EK\to J_FC_YK.$$
For the unit equation, naturality of $\theta_F^{-1}$ for $b^0_M$, then the two displayed unit identities and the unit equation for $\widetilde c^0$, give
$$\begin{aligned}
J_F(b^0_M)c^0_{P_EM}C_X(\eta_E^J(M))
&=\theta_{F,P_FC_XM}^{-1}G_F(b^0_M)\widetilde c^0_{P_EM}C_X(\eta_E^G(M))\\
&=\theta_{F,P_FC_XM}^{-1}\eta_F^G(C_XM)=\eta_F^J(C_XM).
\end{aligned}$$
For the counit equation use $\epsilon_F^JP_F(\theta_F^{-1})=\epsilon_F^G$, the counit equation for $\widetilde c^0$, and naturality of $b^0$ for $\theta_{E,K}$:
$$\begin{aligned}
\epsilon_F^J(C_YK)P_F(c^0_K)b^0_{J_EK}
&=\epsilon_F^G(C_YK)P_F(\widetilde c^0_K)P_FC_X(\theta_{E,K})b^0_{J_EK}\\
&=\epsilon_F^G(C_YK)P_F(\widetilde c^0_K)b^0_{G_EK}C_YP_E(\theta_{E,K})\\
&=C_Y(\epsilon_E^G(K)P_E(\theta_{E,K}))=C_Y(\epsilon_E^J(K)).
\end{aligned}$$
For consecutive extensions, inserting the definition of $c^0$ leaves adjacent scalar-extended factors $\theta_F\theta_F^{-1}$; their cancellation and the composition equation for $\widetilde c^0$ give that for $c^0$. We can therefore use $b^0,c^0$ with the normalized right adjoints $J_R$.

Uses: det-sp-field-extension-towers, prop-coef-integral-exceptional-adjoint, det-sp-unique-right-adjoint, lem-weil-finite-free-completed-scalar-comparison

### Original step 3

Define the integral comparison for the twisted pullback by
$$a^0_K=\gamma_{F,C_YK}^{-1}\circ c^0_K\circ C_X(\gamma_{E,K}):C_XH_EK\xrightarrow{\sim}H_FC_YK.$$
It is natural and invertible, being a composite of natural isomorphisms. The unit identity is the following calculation, using naturality of $\gamma_F^{-1}$ for $b^0_M$ and the normalized unit equation from Step 2:
$$\begin{aligned}
H_F(b^0_M)a^0_{P_EM}C_X(\eta_E^H(M))
&=\gamma_{F,P_FC_XM}^{-1}J_F(b^0_M)c^0_{P_EM}C_X(\gamma_{E,P_EM}\eta_E^H(M))\\
&=\gamma_{F,P_FC_XM}^{-1}J_F(b^0_M)c^0_{P_EM}C_X(\eta_E^J(M))\\
&=\gamma_{F,P_FC_XM}^{-1}\eta_F^J(C_XM)=\eta_F^H(C_XM).
\end{aligned}$$
For the counit, cancel $P_F(\gamma_F)P_F(\gamma_F^{-1})$, use naturality of $b^0$ for $\gamma_{E,K}$, and then Step 2's counit equation:
$$\begin{aligned}
\epsilon_F^H(C_YK)P_F(a^0_K)b^0_{H_EK}
&=\epsilon_F^J(C_YK)P_F(c^0_K)P_FC_X(\gamma_{E,K})b^0_{H_EK}\\
&=\epsilon_F^J(C_YK)P_F(c^0_K)b^0_{J_EK}C_YP_E(\gamma_{E,K})\\
&=C_Y(\epsilon_E^J(K)P_E(\gamma_{E,K}))=C_Y(\epsilon_E^H(K)).
\end{aligned}$$
These are compatibility equations for the actual twisted-pullback adjunction.

Uses: det-sp-integral-adjunction-bijection, det-sp-field-extension-towers

### Original step 4

Let $Q_R$ denote raw scalar localization. By the rational-category definition every rational object has an integral representative, with exactly the same object set and Hom groups $\operatorname{Hom}_{\mathcal O_R}(U,V)\otimes_{\mathcal O_R}R$. Rational compact supports, pullback and twists are the integral operations followed by $Q_R$, and $C^T_{F/E}$ on objects and morphisms is the rationalization of $C_T$. Therefore define $b_{F/E,M}=Q_F(b^0_{M_0})$ and $a_{F/E,K}=Q_F(a^0_{K_0})$ on the integral representatives $M_0,K_0$. These have exactly the two endpoints in the statement. Their inverses are $Q_F((b^0_{M_0})^{-1})$ and $Q_F((a^0_{K_0})^{-1})$: the localization composition formula sends both integral inverse equations to inverse equations. For an integral morphism $u$ the naturality square is the image of the integral square; for $u\otimes\lambda$, $\lambda\in E\subset F$, both sides are that image multiplied by $\lambda$. Every rational morphism is a finite sum of such tensors, so addition proves naturality for every rational morphism, including every rational isomorphism between representatives. Hence no choice of a lift of a rational isomorphism is needed.

Uses: def-weil-rationalization-karoubi, def-weil-linear-scalar-localization, def-weil-integral-rational-qbar-compact-support, def-weil-derived-pullback-tensor-hom, def-coefficient-twists-detailed

### Original step 5

The integral Hom bijection is linear, as is needed before tensoring it. For the compactification used in $P_R$, the strict compact-support tower functor is $\mathcal O_R$-linear [lem-weil-compact-support-reduction-tower-functor]. Its derived inverse limit is computed on K-injective tower resolutions by termwise limit [lem-weil-pbc-ringed-strict-tower-homotopy-limit]. A scalar multiple of a map between such representatives induces the same scalar multiple on the limit; addition is respected for the same reason. Hence the integral compact-support construction makes $P_R$ linear. The inverse-transpose map $v\mapsto\epsilon_R^H(K_0)\circ P_R(v)$ is therefore linear. It is bijective, so its inverse is linear as well. Tensor the resulting integral adjunction isomorphism $\operatorname{Hom}(P_RM_0,K_0)\cong\operatorname{Hom}(M_0,H_RK_0)$ with $R$ over $\mathcal O_R$. The localized Hom formulas identify its ends with $\operatorname{Hom}(Rf_{!,R}M,K)$ and $\operatorname{Hom}(M,Lf_R^*K(d)[2d])$. Naturality holds for integral maps by the original adjunction, and for arbitrary localized maps by the finite-sum calculation of Step 4. Its inverse is the tensor of the inverse isomorphism, so this is an adjunction. Taking the images of identity morphisms under these inverse bijections shows that its unit and counit are precisely $Q_R(\eta_R^H)$ and $Q_R(\epsilon_R^H)$. Apply $Q_F$ to the two equations of Step 3. The localization formula preserves composition and identities, and its functors act on an integral map by its integral image tensored with $1$. Thus the resulting equations are exactly the rational unit and counit compatibility claimed in the statement.

Uses: det-sp-integral-adjunction-bijection, def-weil-rationalization-karoubi, def-weil-linear-scalar-localization, lem-weil-compact-support-reduction-tower-functor, lem-weil-pbc-ringed-strict-tower-homotopy-limit, def-weil-integral-rational-qbar-compact-support

### Original step 6

For $E\subset F\subset L$, let $C_1^T=C^T_{F/E}$, $C_2^T=C^T_{L/F}$ and $C_{21}^T=C^T_{L/E}$ denote integral coefficient extension in this step, and let $\alpha_T:C_2^TC_1^T\xrightarrow{\sim}C_{21}^T$ be the integral associator, transported from ordinary tensor extension using the natural isomorphisms $\chi$ of [lem-weil-finite-free-completed-scalar-comparison]. Explicitly, writing $T_1,T_2,T_{21}$ for ordinary tensor extension and $\alpha^t:T_2T_1\to T_{21}$, this is
$$
 \alpha=\chi_{21}\circ\alpha^t\circ T_2(\chi_1^{-1})\circ\chi_{2,C_1}^{-1}:C_2C_1\longrightarrow C_{21}.
$$
This is the completed-tensor associator on integral representatives whose rationalization is the canonical associator of [lem-weil-scalar-extension-composition]. Thus the composition equations used below are precisely the tensor-version equations conjugated by the specified comparisons, with no appeal to faithfulness of reduction. Suppressing its canonical endpoint identifications temporarily, direct substitution gives
$$\begin{aligned}
a^0_{L/F,C_1^YK}\,C_2^X(a^0_{F/E,K})
&=\gamma_L^{-1}c^0_{L/F}\,C_2^X(\gamma_F)\,C_2^X(\gamma_F^{-1})\,C_2^X(c^0_{F/E})\,C_2^XC_1^X(\gamma_E)\\
&=\gamma_L^{-1}c^0_{L/F}\,C_2^X(c^0_{F/E})\,C_2^XC_1^X(\gamma_E).
\end{aligned}$$
The intermediate factors cancel directly; no extra naturality identity for $c^0$ is required. Restoring associators, the composition equation for $c^0$ from Step 2 and naturality of $\gamma_L^{-1}$ for $\alpha_Y$ turn the last expression into the typed equation
$$H_L(\alpha_{Y,K})\circ a^0_{L/F,C_1^YK}\circ C_2^X(a^0_{F/E,K})=a^0_{L/E,K}\circ\alpha_{X,H_EK}.$$
The composition equation for $b^0$ is directly the integral field-extension theorem's clause (2):
$$P_L(\alpha_{X,M})\circ b^0_{L/F,C_1^XM}\circ C_2^Y(b^0_{F/E,M})=b^0_{L/E,M}\circ\alpha_{Y,P_EM}.$$
Apply $Q_L$, which preserves composition. The scalar-extension composition theorem identifies these localized integral associators with those for rational coefficient extension. The two displayed equations are precisely the required rational cocycles. Under the coefficient-extension unit identifications, the composition identities for an identity extension read $b^0=b^0b^0$ and $c^0=c^0c^0$; invertibility cancels one factor and makes both identities. Conjugation by $\gamma$ gives the identity for $a^0$. This covers $F=E$ and $L=F$.

Uses: det-sp-field-extension-towers, lem-weil-scalar-extension-composition, def-weil-linear-scalar-localization, lem-weil-finite-free-completed-scalar-comparison

## Unfinished work

The three extracted prerequisite proofs are intentionally unsplit stage-1 work for subsequent workers. This delivery writes no Lean and runs no compiler. The parent assembly is complete conditional on the cited prerequisite statements.

## Route repair after second dry run

The second dry run found that realizing the key unit made its previously missing route to sk-prop-sp-rational visible. I opened det-sp-rational-localized-hom in full: it supplies essential integral models, the actual B-linear map h tensor lambda to lambda h[1/ell], and canonical pullback/compact-support endpoint comparisons, explicitly identifying its integral category with derived-complete constructibles. The rationalized-diagrams node now uses that statement for a precise final comparison clause: rhoX composed with (PhiH tensor 1) composed with rhoY inverse is the same localized Hom bijection as the rational-purity route. It does not identify condensed and raw categories by notation or assert that the source theorem supplies an adjunction. This makes the unit route a real mathematical comparison, while the integral-to-rational argument remains the same. The additional queries were run and logged; none gives this normalized geometric Hom comparison. The source proof for det-sp-rational-localized-hom and its live declaration were read; the parent proof is unchanged.
