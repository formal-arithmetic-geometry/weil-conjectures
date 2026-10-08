+++
id = "sk-def-pairing"
kind = "section"
title = "The derived pairing, and perfectness of a pairing"
order = 2418
uses = ["sk-def-pairing-data", "sk-def-perfect"]
+++
*Definition (sketch).*

In the setting of [sk-def-pairing-data], for $K$ perfect over
$\Lambda_X$ the *derived Poincaré pairing* is the composite

$$
\begin{aligned}
\beta_K:\ \RGammac(X,K)\otimes^L_\Lambda\RGamma\bigl(X,K^\vee(d)\bigr)[2d]
&\xrightarrow{\ \smile_c\ }
\RGammac\bigl(X,K\otimes^L K^\vee(d)\bigr)[2d]\\
&\xrightarrow{\ \RGammac(\ev_K(d))[2d]\ }
\RGammac\bigl(X,\Lambda_X(d)\bigr)[2d]
\xrightarrow{\ \Trsm_{a_X,\Lambda}\ }\Lambda,
\end{aligned}
$$

that is, $\beta_K=\Trsm_{a_X,\Lambda}\circ\RGammac(\ev_K(d))[2d]\circ\smile_c$.
The evaluation arrow lands in $\RGammac(X,\Lambda_X(d))[2d]$, whose
cohomology is not concentrated in degree $0$ (for $X=\mathbf P^1_k$,
$d=1$, $K=\Lambda_X$ it lives in degrees $-2$ and $0$); the
normalized smooth trace of [sk-def-pairing-data] selects the top-degree
summand and fixes the normalization.

A morphism $b:C\otimes^L_\Lambda D\to\Lambda$ of perfect point complexes
is *perfect* if its tensor–internal-Hom adjoint $D\to C^\vee$ is an
isomorphism. (Blueprint 13, def:sf-pairing.)

Uses: [sk-def-pairing-data], [sk-def-perfect]
