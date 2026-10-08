+++
id = "lemma-nagata-quasi-affine-immersion-affine-space-exists"
kind = "lemma"
title = "Existence of an affine-space immersion for a quasi-affine scheme, [stacks-project]"
order = 185
lean = ["AlgebraicGeometry.exists_immersion_affineSpace_of_quasiAffine"]
uses = ["def-nagata-relative-affine-space"]
+++
Let $X$ be a quasi-affine scheme and let $X\to S$ be a morphism that is
locally of finite type. There is an integer $n$ and an immersion
$X\to\mathbb A^n_S$ over $S$.

## Proof

Write $A=\Gamma(X,\mathcal O_X)$, so that $X$ is quasi-compact and
separated and $X\to\operatorname{Spec}(A)$ is an open immersion. The
affine basic opens $X_f$, $f\in A$, form a basis of the topology of $X$,
so every point of $X$ has an affine basic open neighbourhood whose image
in $S$ is contained in an affine open of $S$. By quasi-compactness choose
finitely many $f_1,\ldots,f_m\in A$ and affine opens
$V_1,\ldots,V_m\subseteq S$ such that $X=\bigcup_jX_{f_j}$, each
$X_{f_j}$ is affine and $X_{f_j}\subseteq\pi^{-1}(V_j)$. Since $\pi$ is
locally of finite type, each $\Gamma(X_{f_j},\mathcal O_X)$ is an algebra
of finite type over $\Gamma(V_j,\mathcal O_S)$; choose finitely many
generators. Since $X$ is quasi-compact and quasi-separated,
$\Gamma(X_{f_j},\mathcal O_X)$ is the localization $A_{f_j}$, so after
multiplying by a power of $f_j$ each generator is the restriction of a
global section of $X$; collect these numerators $a_{jk}\in A$. Let
$n=m+\sum_jN_j$ and let $i\colon X\to\mathbb A^n_S$ be the morphism over
$S$ determined by the global sections
$f_1,\ldots,f_m,a_{11},\ldots,a_{mN_m}$.

Being an immersion is Zariski-local on the target, so it suffices to
exhibit, around every point of $X$, an open $W\subseteq\mathbb A^n_S$
whose full preimage under $i$ maps to $W$ by an immersion. For each $j$
let $W_j\subseteq\mathbb A^n_S$ be the affine open of points lying over
$V_j$ at which the $j$-th coordinate is invertible. Then
$i^{-1}(W_j)=X_{f_j}$, and the restriction $X_{f_j}\to W_j$ is a morphism
of affine schemes whose ring map is surjective: its image contains the
image of $\Gamma(V_j,\mathcal O_S)$, the restrictions of the chosen global
sections, and the inverse of the unit $f_j|_{X_{f_j}}$, and these generate
$A_{f_j}$. Hence $X_{f_j}\to W_j$ is a closed immersion and
$X_{f_j}\to\mathbb A^n_S$ is an immersion, as required.
