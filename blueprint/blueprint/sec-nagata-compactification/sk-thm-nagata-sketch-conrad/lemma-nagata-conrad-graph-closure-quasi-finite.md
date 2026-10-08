+++
id = "lemma-nagata-conrad-graph-closure-quasi-finite"
kind = "lemma"
title = "The closed graph is quasi-finite over the blow-up (Conrad)"
order = 217
lean = ["AlgebraicGeometry.exists_isAdmissible_locallyQuasiFinite_image_graph"]
uses = ["def-nagata-admissible-blowup", "def-nagata-effective-cartier-ideal", "def-nagata-extended-ideal", "def-nagata-global-blowup", "def-nagata-invertible-ideal", "def-nagata-quasi-affine-morphism", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "lemma-nagata-affine-blowup-complement", "lemma-nagata-affine-finite-type-is-quasi-affine", "lemma-nagata-blowup-proper", "lemma-nagata-conrad-quasi-affine-general", "lemma-nagata-ideal-invertible-product-factor", "lemma-nagata-ideal-unit-off-support", "lemma-nagata-invertible-product-factor", "lemma-nagata-scheme-image-ideal-qc", "prop-nagata-global-blowup-cover-independent", "thm-nagata-blowup-principalizes-center", "thm-nagata-blowup-universal-property", "thm-nagata-global-blowup-proper"]
+++
Let $X$ be qcqs, let $U\subseteq V\subseteq X$ be quasi-compact opens, let
$p\colon Y\to X$ be separated and locally of finite type with $Y$ qcqs, and
let $f\colon U\to Y$ be a section of $p$ over $U$ whose image is closed in
$p^{-1}(V)$. There is a $V$-admissible blow-up
$q\colon\widetilde X=\operatorname{Bl}_{\mathcal I}(X)\to X$ with the
following property. Let $\sigma\colon U\hookrightarrow\widetilde X$ be the
canonical section of $q$ over $U$, let
$F=(f,\sigma)\colon U\to Y\times_X\widetilde X$ be the induced quasi-compact
immersion, and let $\overline{F(U)}$ be its scheme-theoretic image. Then

$$
\overline{F(U)}\longrightarrow\widetilde X
$$

is quasi-finite (locally quasi-finite, locally of finite type and
quasi-compact) and separated.

Neither $U$ nor $V$ is assumed dense in $X$.

## Proof

Choose a finite affine open cover $\{Z\}_{Z\in S}$ of $Y$ and fix one of its
members $Z$. Since $Z$ is affine it is quasi-affine, and the composite
$p_Z\colon Z\hookrightarrow Y\xrightarrow{p}X$ is quasi-compact because $Z$
is quasi-compact and $X$ is quasi-separated; so $p_Z$ is quasi-affine as a
morphism ([def-nagata-quasi-affine-morphism]). Put
$U_Z=U\cap f^{-1}(Z)$, an open of $X$ contained in $U$, hence in $V$, and
quasi-compact because $f$ is quasi-compact. The restriction
$f_Z\colon U_Z\to Z$ of $f$ is a section of $p_Z$ over $U_Z$, and its image
is the trace of $f(U)$ on $Z$, hence closed in $p_Z^{-1}(V)=Z\cap p^{-1}(V)$.

So [lemma-nagata-conrad-quasi-affine-general] applies to
$(U_Z\subseteq V, f_Z, p_Z)$ and produces a finite type quasi-coherent ideal
$\mathcal I_Z$ on $X$ with $V(\mathcal I_Z)\cap V=\varnothing$, an open
$W_Z\subseteq\operatorname{Bl}_{\mathcal I_Z}(X)$ containing the preimage of
$U_Z$, and an $X$-morphism $g_Z\colon W_Z\to Z$ extending $f_Z$ whose graph is
closed in $Z\times_X\operatorname{Bl}_{\mathcal I_Z}(X)$.

*Unlike Conrad we do not replace $X$ by the scheme-theoretic image
$\overline{U_Z}$.* Conrad does so in order to make $U_Z$ dense, which his
quasi-affine case requires; the form of that case proved here
([lemma-nagata-conrad-quasi-affine-general]) carries no density
hypothesis, so the reduction to the smaller base — and with it the
extension of $\mathcal I_Z$ from $\overline{U_Z}$ back to $X$ and the
ambient closedness of the strict transform — is unnecessary.

Put $\mathcal I=\prod_{Z\in S}\mathcal I_Z$; it is of finite type and
$V(\mathcal I)=\bigcup_ZV(\mathcal I_Z)$ misses $V$, so
$q\colon\widetilde X=\operatorname{Bl}_{\mathcal I}(X)\to X$ is a
$V$-admissible blow-up. For each $Z\in S$ the inverse image of
$\mathcal I_Z$ on $\widetilde X$ is a factor of the invertible ideal
$\mathcal I\cdot\mathcal O_{\widetilde X}$, hence invertible
([lemma-nagata-invertible-product-factor]), so the universal property of
blowing up ([thm-nagata-blowup-universal-property]) provides a
comparison $c_Z\colon\widetilde X\to\operatorname{Bl}_{\mathcal I_Z}(X)$ over
$X$.

Write $\Omega_Z=\mathrm{pr}_Y^{-1}(Z)\subseteq Y\times_X\widetilde X$, an open
subscheme, and let $\Phi_Z$ be the graph of
$c_Z^{-1}(W_Z)\to W_Z\xrightarrow{g_Z}Z$, a morphism
$c_Z^{-1}(W_Z)\to Y\times_X\widetilde X$ landing in $\Omega_Z$ and satisfying
$\mathrm{pr}_{\widetilde X}\circ\Phi_Z=\iota_{c_Z^{-1}(W_Z)}$. Two things
hold.

1. *$\Phi_Z$ is injective over $\widetilde X$*: this is immediate
from $\mathrm{pr}_{\widetilde X}\circ\Phi_Z=\iota_{c_Z^{-1}(W_Z)}$.
1. *The range of $\Phi_Z$ is closed in $\Omega_Z$*: indeed
$\Omega_Z=Z\times_X\widetilde X$ and
$c_Z^{-1}(W_Z)=W_Z\times_{\operatorname{Bl}_{\mathcal I_Z}(X)}\widetilde X$,
so $\Phi_Z$ is the base change of the closed graph of $g_Z$ along
$\Omega_Z\to Z\times_X\operatorname{Bl}_{\mathcal I_Z}(X)$, and the range
of a base change is the inverse image of the range.

Finally, $F(U)\cap\Omega_Z$ is contained in the range of $\Phi_Z$: a point of
it is $F(u)$ with $f(u)\in Z$, so $u\in U_Z$, and there $\sigma$ lands in
$c_Z^{-1}(W_Z)$ and $g_Z$ agrees with $f$. As $\Omega_Z$ is open,
$\overline{F(U)}\cap\Omega_Z$ is the closure of $F(U)\cap\Omega_Z$ inside
$\Omega_Z$, which by (2) is again contained in the range of $\Phi_Z$. The
$\Omega_Z$ cover $Y\times_X\widetilde X$, so the underlying space of
$\overline{F(U)}$ is covered by the finitely many sets $\Phi_Z(c_Z^{-1}(W_Z))$,
each injective over $\widetilde X$ by (1); hence the fibres of
$\overline{F(U)}\to\widetilde X$ are finite. Being locally of finite type
(as a closed immersion followed by a base change of $p$), the morphism is
therefore locally quasi-finite. It is quasi-compact because
$\overline{F(U)}$ is quasi-compact and $\widetilde X$ quasi-separated, and
separated because $p$ is.
