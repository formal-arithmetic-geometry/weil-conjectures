+++
id = "lem-a1-affine-hc2"
kind = "lemma"
title = "Description of $H_c^2$ on an affine curve"
order = 2653
uses = ["def-compact-support-direct-image-detailed", "def-pod-conventions", "def-weil-extension-by-zero", "def-weil-ordinary-compact-cohomology", "def-wf-fundamental-representation", "def-wf-monodromy-data", "def-wf-tate-twist", "fix-cor-verdier-exchange", "fix-lem-exchanges", "lem-weil-derived-direct-image-composition", "lem-wf-curve-normal-smooth-compactification", "p-real-sections", "prop-exc-open-adjoint", "thm-pod-global-verdier-duality"]
+++
Let $U_0$ be a smooth geometrically connected affine curve, let
$U=U_0\times_{k_0}k$, and let $\mathcal F$ be a lisse Weil sheaf on
$U_0$ with local generic fiber $V=\mathcal F_{\bar\eta}$ (a
geometric generic stalk of [def-wf-fundamental-representation]).
In the compactly
supported cohomology of
[def-weil-ordinary-compact-cohomology] there is a canonical
Frobenius-equivariant isomorphism

$$
H_c^2(U,\mathcal F)\;\simeq\;V_{\pi_1(U)}(-1),
$$

where the coinvariants are formed for the geometric monodromy action of
[def-wf-monodromy-data] and $(-1)$ is the
Tate twist $(-1)$.

## Proof

We work through a smooth compactification (global Verdier duality
would also apply directly on $U$, which need not be proper, but the
argument below only needs it on $\bar C$). By [lem-wf-curve-normal-smooth-compactification]
there are a smooth projective geometrically connected curve $\bar C_0$
over $k_0$ and a dense open immersion $j_0:U_0\hookrightarrow\bar C_0$
with finite boundary; put $\bar C=\bar C_0\times_{k_0}k$, let
$j:U\hookrightarrow\bar C$ be the base change of $j_0$, and let
$a_U=a_{\bar C}\circ j$ be the structure morphisms. Then $\bar C_0$
satisfies the hypotheses of the Poincare duality conventions of
[def-pod-conventions] with $d=1$, and we use its canonical orientation
$\eta_{\bar C}:\omega_{\bar C}\xrightarrow{\sim}E_{\bar C}(1)[2]$.

*Step 1 (compact support through $\bar C$).* For the open immersion
$j$ the identity of $\bar C$ is a compactification, so the compact-support
direct image of [def-compact-support-direct-image-detailed] is
$Rj_!=j_!$, the extension by zero of [def-weil-extension-by-zero]. The
composition law for compact-support direct images ([fix-lem-exchanges])
gives $Ra_{U!}\mathcal F\simeq Ra_{\bar C!}\,j_!\mathcal F$, hence, by
[def-weil-ordinary-compact-cohomology],

$$
R\Gamma_c(U,\mathcal F)\simeq R\Gamma_c(\bar C,j_!\mathcal F),
$$

where $j_!\mathcal F$ is a constructible (not lisse) sheaf on the proper
curve $\bar C$.

*Step 2 (duality on $\bar C$).* Apply [thm-pod-global-verdier-duality]
on the proper $\bar C$ to $K=j_!\mathcal F$, which that theorem allows
since it is stated for every $K\in D^b_{ctf}(\bar C,\Lambda)$:

$$
R\Gamma_c(\bar C,j_!\mathcal F)^\vee\simeq
R\Gamma\bigl(\bar C,\mathbb D_{\bar C}(j_!\mathcal F)\bigr).
$$

The Verdier-duality exchange [fix-cor-verdier-exchange] for $f=j$ gives
$\mathbb D_{\bar C}(j_!\mathcal F)\simeq Rj_*\mathbb D_U\mathcal F$
with $\mathbb D_U=R\mathcal Hom(-,\omega_U)$ and
$\omega_U\simeq Rj^!\omega_{\bar C}$ (step 1 of its proof). For an open
immersion the right adjoint of $j_!$ is $j^*$
([prop-exc-open-adjoint]), so $\omega_U\simeq j^*\omega_{\bar C}$, and
$j^*\eta_{\bar C}$ gives $\omega_U\simeq E_U(1)[2]$. As $\mathcal F$ is
lisse, $R\mathcal Hom(\mathcal F,E_U)=\mathcal F^\vee$, so
$\mathbb D_U\mathcal F\simeq\mathcal F^\vee(1)[2]$. Finally
$Ra_{\bar C*}Rj_*\simeq Ra_{U*}$ by the composition isomorphism
[lem-weil-derived-direct-image-composition] for $a_U=a_{\bar C}\circ j$,
which applies because $Rj_*\mathbb D_U\mathcal F\simeq
\mathbb D_{\bar C}(j_!\mathcal F)$ is constructible. Hence

$$
R\Gamma_c(U,\mathcal F)^\vee\simeq
R\Gamma\bigl(U,\mathcal F^\vee(1)\bigr)[2].
$$

*Step 3 (degree $-2$).* Taking $H^{-2}$ (over the field $E$ or $\Qlb$
dualizing commutes with cohomology) gives
$H_c^2(U,\mathcal F)^\vee\simeq H^0(U,\mathcal F^\vee(1))$. Global
sections of a lisse sheaf are the invariants of the geometric
representation of [def-wf-fundamental-representation] [p-real-sections],
so $H^0(U,\mathcal F^\vee(1))=(V^\vee(1))^{\pi_1(U)}$, the geometric
monodromy action being that of [def-wf-monodromy-data]. Dualizing turns
invariants of $V^\vee$ into coinvariants of $V$, and turns the twist
$(1)$ into $(-1)$, which gives the displayed isomorphism. All maps above
are canonical and $\bar C$, $j$, $\eta_{\bar C}$ are base changed from
$k_0$, so the isomorphism commutes with the Frobenius operators induced
by the Weil structures, with the twist normalized as in
[def-wf-tate-twist].
