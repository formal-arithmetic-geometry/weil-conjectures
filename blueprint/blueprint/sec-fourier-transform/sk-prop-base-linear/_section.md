+++
id = "sk-prop-base-linear"
kind = "section"
title = "P7: the transform is linear over the base"
order = 2704
lean = ["AlgebraicGeometry.Etale.fourierTransformTensorIso"]
uses = ["sk-def-ft"]
+++
*Proposition (sketch).*

Let $p:V\to S$ and $p':V^\vee\to S$ be the structure morphisms. For
$K\in\Dbc(V,E)$ and $N\in\Dbc(S,E)$,

$$
\FT_\psi\bigl(K\otimes^Lp^*N\bigr)\cong\FT_\psi(K)\otimes^L{p'}^*N .
$$

In particular, for $N$ from the base,
$\FT_\psi(p^*N)\cong\FT_\psi(\underline{E})\otimes^L{p'}^*N$, so the
transform of a base-changed sheaf is the base change of the transform of the
unit.

## Proof

On the Fourier square one has $p\circ p_1=p'\circ p_2$, hence
$p_1^*\bigl(K\otimes^Lp^*N\bigr)\cong p_1^*K\otimes^Lp_2^*{p'}^*N$. Tensoring
with the kernel and applying the projection formula of
prop:functor-package to the compact-support direct image $p_{2,!}$ with
first variable $p_1^*K\otimes^L\mathcal K_\psi$ and second variable
${p'}^*N$ — legitimate because $p_2$ is separated of finite type and
${p'}^*N$ has finite Tor amplitude — gives
$p_{2,!}\bigl(p_1^*K\otimes^L\mathcal K_\psi\bigr)\otimes^L{p'}^*N$, and the
shift $[r]$ commutes with the tensor product by a constant.

Uses: [sk-def-ft]
