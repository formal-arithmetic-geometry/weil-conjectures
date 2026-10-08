+++
id = "cor-fd-l2-plancherel-middle-extension"
kind = "theorem"
title = "Plancherel for a middle extension: the transform shifts the weight of a pure lisse sheaf by exactly one"
order = 2779
tags = ["latex:corollary"]
uses = ["def-fd-trace-function", "def-fd-transform", "def-weil-punctual-weights", "def-wf-l2-norm", "def-wf-middle-extension", "lem-fd-l2-middle-extension", "lem-fd-l2-plancherel-shift", "lem-wf-l2-purity-rigidity", "prop-a1-fourier-middle-extension", "thm-fd-generic-fourier-sheaf-pure"]
+++
Let $j:U_0\hookrightarrow\mathbf A^1_{k_0}$ be a dense open immersion
with finite complement, and let $\mathcal M$ be a lisse Weil sheaf on
$U_0$, punctually $\iota$-pure
of weight $w$. Suppose that the Fourier–Deligne transform of its
middle extension has the
middle-extension shape

$$
\operatorname{FT}_\psi\bigl(j_*\mathcal M[1]\bigr)\cong j'_*\mathcal M'[1]
$$

with $\mathcal M'$ lisse on a dense open
$U_0'\hookrightarrow\mathbf A^1_{k_0}$, punctually $\iota$-pure of
weight $v$. Then

$$
v=w+1 .
$$

The middle-extension shape holds, with $\mathcal M'$ irreducible,
whenever $\mathcal M$ is irreducible and constituent-nonexceptional
([prop-a1-fourier-middle-extension]). In that case the purity of
$\mathcal M'$ is automatic as well: if $\mathcal M$ is nonzero,
irreducible, constituent-nonexceptional and punctually $\iota$-pure of
weight $w$, then the sheaf $\mathcal M'$ of
[prop-a1-fourier-middle-extension] is punctually $\iota$-pure of weight
exactly $w+1$.

## Proof

The trace function of [def-fd-trace-function] is unchanged in
absolute value by the shift $[1]$: the shift multiplies the
alternating trace by $-1$, of $\iota$-modulus one, so
$\|f_{j_*\mathcal M[1]}\|_m=\|f_{j_*\mathcal M}\|_m$ and likewise
$\|f_{j'_*\mathcal M'[1]}\|_m=\|f_{j'_*\mathcal M'}\|_m$ for every
$m$. The Plancherel shift [lem-fd-l2-plancherel-shift], applied
to the Weil complex $j_*\mathcal M[1]$, therefore reads

$$
\|j'_*\mathcal M'\|
=\bigl\|\operatorname{FT}_\psi(j_*\mathcal M[1])\bigr\|
=\|j_*\mathcal M\|+1 .
$$

By the middle-extension comparison [lem-fd-l2-middle-extension],
$\|j_*\mathcal M\|=\|\mathcal M\|=w$ and
$\|j'_*\mathcal M'\|=\|\mathcal M'\|=v$, the second equality in each
case being the rigidity [lem-wf-l2-purity-rigidity] applied to the
punctually pure lisse sheaf $\mathcal M$ respectively $\mathcal M'$.
Substituting, $v=w+1$.

For the last assertion, [prop-a1-fourier-middle-extension] supplies the
middle-extension shape with $\mathcal M'$ lisse on the dense open
$U'_0$, and [thm-fd-generic-fourier-sheaf-pure] shows that
$\mathcal M'$ is punctually $\iota$-pure of some real weight $v$ on all
of $U'_0$. All hypotheses of the first part are then met, so $v=w+1$.
