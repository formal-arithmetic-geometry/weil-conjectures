+++
id = "lem-fd-kernel-composition"
kind = "lemma"
title = "Composition of kernel transforms"
order = 2712
lean = ["AlgebraicGeometry.Etale.kernelTransformCompIso"]
uses = ["def-fd-kernel", "def-fd-transform", "prop-functor-package"]
+++
Let $V\to S$, $V^\vee\to S$, $V''\to S$ be separated finite-type
$S$-schemes, let $\mathcal K\in D^b_c(V\times_SV^\vee,E)$ and
$\mathcal K'\in D^b_c(V^\vee\times_SV'',E)$, and let

$$
\Phi_{\mathcal K}(K)=p_{2,!}(p_1^*K\otimes^L\mathcal K)[a],\qquad
\Phi_{\mathcal K'}(L)=q_{2,!}(q_1^*L\otimes^L\mathcal K')[b]
$$

be the corresponding kernel transforms, with $p_i,q_i$ the projections of
$V\times_SV^\vee$ and $V^\vee\times_SV''$ and shifts $a,b$. Then
$\Phi_{\mathcal K'}\circ\Phi_{\mathcal K}$ is the kernel transform with
kernel the *convolution*

$$
\mathcal K'\ast\mathcal K:=r_{13,!}\bigl(r_{12}^*\mathcal K\otimes^L
r_{23}^*\mathcal K'\bigr)\in D^b_c(V\times_SV'',E)
$$

and shift $[a+b]$, the $r_{ij}$ being the projections of the triple
product $V\times_SV^\vee\times_SV''$. In particular
$\operatorname{FT}_{\psi^{-1}}\operatorname{FT}_\psi$ is the kernel
transform with kernel $\mathcal K_{\psi^{-1}}\ast\mathcal K_\psi$ and shift
$[2r]$.

## Proof

Substituting the definitions and using
$p_2\circ r_{12}=r_2=q_1\circ r_{23}$, the base change of
[prop-functor-package] for the compact-support direct image along $q_1$
gives $q_1^*p_{2,!}\cong r_{23,!}r_{12}^*$, and the projection formula of
[prop-functor-package] for $r_{23}$ moves $r_{23}^*\mathcal K'$
inside; the composition law $q_2\circ r_{23}=r_3$ then gives

$$
\Phi_{\mathcal K'}\Phi_{\mathcal K}(K)
=r_{3,!}\bigl(r_1^*K\otimes^Lr_{12}^*\mathcal K\otimes^L
r_{23}^*\mathcal K'\bigr)[a+b],
\qquad r_1=p_1\circ r_{12}.
$$

The kernel transform with kernel $\mathcal K'\ast\mathcal K$ has the same
value: the projection formula for $r_{13}$ together with
$r_{13}^*s_1^*\cong r_1^*$, $s_2\circ r_{13}=r_3$ and the composition law
turns it into the same expression. Comparing the two expressions identifies
the kernels, and the shift is $[a]+[b]$ because the two shifts are those of
the two factors.
