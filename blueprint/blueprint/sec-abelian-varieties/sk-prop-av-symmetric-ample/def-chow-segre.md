+++
id = "def-chow-segre"
kind = "definition"
title = "Segre embedding"
order = 476
lean = ["AlgebraicGeometry.ProjectiveSpace.segre"]
uses = ["def-nagata-affine-proj", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-projective-space-base-change", "def-weil-pbc-scheme-conventions", "prop-nagata-proj-standard-open"]
+++
Let $S$ be a scheme and let $n$ and $m$ be index sets for the homogeneous
coordinates of $\mathbf P^{n}_S$ and $\mathbf P^{m}_S$. The *Segre
embedding* is the morphism of $S$-schemes

$$
s\colon\mathbf P^{n}_S\times_S\mathbf P^{m}_S
\longrightarrow\mathbf P^{n\times m}_S,
\qquad
\bigl((x_k)_{k\in n},(y_l)_{l\in m}\bigr)
\longmapsto
\bigl[x_k\,y_l\bigr]_{(k,l)\in n\times m} .
$$

In the classical indexing this is
$\mathbf P^{n_1}_S\times_S\mathbf P^{n_2}_S\to\mathbf P^{N}_S$ with
$N=(n_1+1)(n_2+1)-1$; iterating it $m-1$ times embeds an $m$-fold product
into $\mathbf P^{N}_S$ with $N=\prod_{i=1}^m(n_i+1)-1$.

## Detailed form

For integers $n_1,\dots,n_m\geq0$, let $N=\prod_{i=1}^m(n_i+1)-1$ and let the
coordinates of $\mathbf P^N_Y$ be $X_{e}$, indexed by tuples
$e=(e_1,\dots,e_m)$ with $0\leq e_i\leq n_i$. The *Segre embedding* is the
morphism of $Y$-schemes

$$
 s:\prod_{i=1}^m\mathbf P^{n_i}_Y\longrightarrow\mathbf P^N_Y,
$$

given by the multihomogeneous coordinates

$$
 x\longmapsto\bigl[\prod_{i=1}^m x_{i,e_i}\bigr]_{e},
 \qquad x=(x_{i,0}:\cdots:x_{i,n_i})_{i=1}^m.
$$
