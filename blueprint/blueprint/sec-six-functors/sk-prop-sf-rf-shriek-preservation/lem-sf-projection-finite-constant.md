+++
id = "lem-sf-projection-finite-constant"
kind = "lemma"
title = "The projection formula with a finitely presented constant coefficient"
order = 2065
uses = ["def-sf-uniform-direct-image-vanishing", "def-weil-derived-pullback-tensor-hom", "def-weil-derived-tensor", "def-weil-pbc-direct-image", "def-weil-pbc-inverse-image", "thm-sp-truncation-e2"]
+++
Let $f:X\to Y$ be a morphism of schemes, let $A$ be a Noetherian
commutative ring, assume $R^qf_*F=0$ for every sheaf of $A$-modules
$F$ and every $q>N$, for one integer $N\geq0$, and let
$K\in D^-(X_{\Et},A)$. Let $M$ be a finitely
presented $A$-module, with $M_X,M_Y$ the associated constant sheaves.
Then the canonical projection map

$$
Rf_*K\otimes^L_AM_Y\longrightarrow Rf_*\bigl(K\otimes^L_AM_X\bigr)
$$

is an isomorphism, the direct image and the tensor product being those of
[def-weil-pbc-direct-image] and [def-weil-derived-tensor] on the
small étale sites. The map is natural in $M$.

## Proof

Specify the map first: it is the mate, under the adjunction
$Lf^*\dashv Rf_*$ of [def-weil-pbc-inverse-image], [def-weil-pbc-direct-image],
of the composite

$$
Lf^*\bigl(Rf_*K\otimes^L_AM_Y\bigr)
\cong Lf^*Rf_*K\otimes^L_ALf^*M_Y
\xrightarrow{\ \epsilon\otimes\operatorname{id}\ }
K\otimes^L_AM_X,
$$

in which the first isomorphism is the compatibility of the derived pullback
with the derived tensor product of [def-weil-derived-pullback-tensor-hom],
the identification $Lf^*M_Y\cong M_X$ is the pullback of a constant
sheaf, and $\epsilon$ is the counit of the adjunction.

Both functors of $M$, namely
$M\mapsto Rf_*K\otimes^L_AM_Y$ and
$M\mapsto Rf_*(K\otimes^L_AM_X)$, are triangulated: the constant-sheaf
functor is exact, the derived pullback and the derived tensor product are
exact, and $Rf_*$ is triangulated. The map specified above is natural in
$M$. For $M=A$ it is the identification
$Rf_*K\otimes^L_AA_Y\cong Rf_*K\cong Rf_*(K\otimes^L_AA_X)$ of the unit,
and for a finite free module $M=A^r$ it is the direct sum of $r$ copies
of that identification, hence an isomorphism. It follows by finite cones
and shifts that it is an isomorphism for every bounded complex of finite
free $A$-modules.

Choose a free resolution $P\to M$ in nonpositive degrees, with each
$P^i$ finite free; Noetherianity supplies the finite syzygies. Put
$P_m=\sigma_{\geq-m}P$, the brutal truncation. The cone $C_m$ of
$P_m\to M$ belongs to $D^{\leq-m-1}(A)$. Choose $b$ with
$K\in D^{\leq b}$. The assumed bound on all sheaves, applied by the
truncation spectral sequence of [thm-sp-truncation-e2], gives
$Rf_*D^{\leq t}\subseteq D^{\leq t+N}$ on bounded-above complexes.
Consequently both

$$
Rf_*K\otimes_A^L(C_m)_Y,
\qquad Rf_*\bigl(K\otimes_A^L(C_m)_X\bigr)
$$

lie in $D^{\leq b+N-m-1}$. Here the tensor bound follows from
bounded-above flat resolutions. For any fixed degree $r$, choose $m$
so large that $b+N-m-1<r-1$. The two maps from the expressions with
$P_m$ to the expressions with $M$ then induce isomorphisms on
$\mathcal H^r$. The projection map for $P_m$ is an isomorphism by
the bounded finite free case. Naturality therefore proves the projection
map for $M$ is an isomorphism on $\mathcal H^r$. This holds for every
$r$, proving the assertion. A finite presentation alone is not a
distinguished triangle; the infinite resolution is controlled here by the
uniform cohomological-dimension bound.
