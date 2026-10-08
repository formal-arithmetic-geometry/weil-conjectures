+++
id = "lem-a1-local-boundary-duality"
kind = "lemma"
title = "Local boundary duality"
order = 2727
uses = ["def-weil-exceptional-inverse-image", "def-weil-open-closed-recollement", "def-wf-tate-twist", "fix-cor-verdier-exchange", "lem-cbc-open-closed-recollement", "lem-fix-weil-operations", "lem-pod-cohomology-of-dual-over-field", "prop-pur-rational-purity-trace-coherence", "prop-sf-closed-immersion-unit", "prop-sf-closed-unit-all-stages", "prop-sf-localization-all-stages", "prop-sf-open-closed-triangle-all-stages", "prop-weil-open-closed-recollement-adjunctions", "rem-dl-a1-conventions", "thm-coef-qbar-verdier", "thm-pur-rational-and-qbar-purity"]
lean = ["AlgebraicGeometry.exists_linearEquiv_dual_stalk_higherDirectImage"]
+++
In the conventions of [rem-dl-a1-conventions], let
$j:U_0\hookrightarrow C_0$ be a dense open immersion of smooth
curves over $k_0$, let $i:Z_0\hookrightarrow C_0$ be the closed
complement with its reduced structure, and let $F$ be a lisse
$\Qlb$-Weil sheaf on $U_0$, with dual $F^\vee$. Put
$A(F)=i^*Rj_*F$ on $Z$. Then there is a canonical
Frobenius-equivariant isomorphism

$$
\mathbb D_Z A(F)\;\simeq\;A(F^\vee)(1)[1].
$$

Consequently, for every missing closed point $s\in Z_0$, with
geometric point $\bar s$ and local geometric Frobenius $F_s$, there is
a canonical perfect $F_s$-equivariant pairing

$$
(j_*F^\vee)_{\bar s}\otimes(R^1j_*F)_{\bar s}
\longrightarrow\Qlb(-1),
$$

equivalently an isomorphism
$(R^1j_*F)_{\bar s}^\vee\simeq(j_*F^\vee)_{\bar s}(1)$. Here
$j_*$ is the ordinary direct image.

## Proof

Work on the geometric curves with $\Qlb$-coefficients and the Weil
structures of [lem-fix-weil-operations]. The Verdier duals, their
biduality, the exceptional functors $Ri^!$ of
[def-weil-exceptional-inverse-image] with $Ri_!=Ri_*\dashv Ri^!$,
and the identity $Rf^!=\mathbb D_Xf^*\mathbb D_Y$ are those of
[thm-coef-qbar-verdier]. Smooth purity
[thm-pur-rational-and-qbar-purity] for the structure map of $U$
gives $\omega_U\simeq\Qlb(1)[2]$, hence, $F$ being lisse,
$\mathbb D_UF\simeq F^\vee(1)[2]$ (the dual of a lisse sheaf is the
finite-rank coefficient dual; see [def-wf-tate-twist] for the twist).

*Step 1: $\mathbb D_CRj_*\simeq j_!\mathbb D_U$.* The exchange
[fix-cor-verdier-exchange] for $f=j$ gives
$\mathbb D_C(j_!M)\simeq Rj_*\mathbb D_UM$. Put
$M=\mathbb D_UG$ for a constructible $G$ on $U$; biduality on $U$
gives $Rj_*G\simeq\mathbb D_Cj_!\mathbb D_UG$. In particular
$Rj_*G$ is bounded constructible, and applying $\mathbb D_C$ and
biduality on $C$ gives $\mathbb D_CRj_*G\simeq j_!\mathbb D_UG$.

*Step 2: $\mathbb D_Zi^*\simeq Ri^!\mathbb D_C$.* By
[thm-coef-qbar-verdier], $Ri^!=\mathbb D_Zi^*\mathbb D_C$, so
biduality on $C$ gives
$Ri^!\mathbb D_CK\simeq\mathbb D_Zi^*K$ for constructible $K$.

*Step 3: $Ri^!j_!G\simeq i^*Rj_*G[-1]$.* First
$Ri^!Rj_*G=0$: for every $N$ on $Z$,

$$
\operatorname{Hom}(N,Ri^!Rj_*G)
\cong\operatorname{Hom}(i_*N,Rj_*G)
\cong\operatorname{Hom}(j^*i_*N,G)=0,
$$

since $j^*i_*=0$, and Yoneda applies. Next, the open–closed
recollement triangle ([def-weil-open-closed-recollement]), which exists at $\Qlb$ with Weil-equivariant arrows by [prop-sf-open-closed-triangle-all-stages] (at a finite stage it is [lem-cbc-open-closed-recollement]), for $K=Rj_*G$, with
$j^*Rj_*G\simeq G$ by the unit/counit identities of
[prop-weil-open-closed-recollement-adjunctions], reads

$$
j_!G\longrightarrow Rj_*G\longrightarrow i_*i^*Rj_*G
\xrightarrow{+1}.
$$

Apply the exact functor $Ri^!$. The middle term vanishes, and the
closed-immersion unit $Q\xrightarrow{\sim}Ri^!Ri_*Q$ at $\Qlb$,
clause (4) of [prop-sf-localization-all-stages] (from the full faithfulness of
[prop-sf-closed-unit-all-stages]; at a finite stage it is
[prop-sf-closed-immersion-unit]), identifies the third term with
$i^*Rj_*G$. Hence $Ri^!j_!G\simeq i^*Rj_*G[-1]$.

*Step 4: the isomorphism.* Combining the steps with
$G=\mathbb D_UF\simeq F^\vee(1)[2]$,

$$
\begin{aligned}
\mathbb D_ZA(F)
&\simeq Ri^!\mathbb D_CRj_*F
\simeq Ri^!j_!\mathbb D_UF\\
&\simeq i^*Rj_*(\mathbb D_UF)[-1]
\simeq A(F^\vee)(1)[1].
\end{aligned}
$$

*Step 5: the stalks.* The reduced scheme $Z$ is finite over the
algebraically closed field $k$, hence a finite disjoint union of
copies of $\operatorname{Spec}k$, smooth of dimension zero. Smooth
purity [thm-pur-rational-and-qbar-purity] in dimension zero gives
$\omega_Z=\Qlb$, so on the component $\bar s$ the functor
$\mathbb D_Z$ is $R\operatorname{Hom}_{\Qlb}(-,\Qlb)$ on bounded
complexes of finite-dimensional spaces. By
[lem-pod-cohomology-of-dual-over-field] (at a finite coefficient
field over which the stalk complex is defined, then extended to
$\Qlb$),

$$
H^{-1}\bigl(\mathbb D_ZA(F)\bigr)_{\bar s}
\simeq H^1(A(F)_{\bar s})^\vee=(R^1j_*F)_{\bar s}^\vee.
$$

On the other side,
$H^{-1}\bigl(A(F^\vee)(1)[1]\bigr)_{\bar s}
=H^0\bigl(Rj_*F^\vee\bigr)_{\bar s}(1)=(j_*F^\vee)_{\bar s}(1)$,
because the ordinary direct image is $\mathcal H^0$ of the derived
one. This is the asserted isomorphism; its transpose is the
asserted perfect pairing, the twist $(1)$ on one side becoming
$(-1)$ in the target.

*Frobenius equivariance.* Every map used is built from pullbacks,
direct images, internal Hom, evaluation, adjunction units and counits,
and exchange maps, all Weil-equivariant by
[lem-fix-weil-operations], together with the smooth-purity
orientations, whose equivariance and trace compatibility are
[prop-pur-rational-purity-trace-coherence]. Hence the isomorphism of
Step 4 is one of Weil complexes on $Z_0$, and its stalk at $\bar s$
commutes with $F_s$; the twists carry their prescribed Frobenius
actions.
