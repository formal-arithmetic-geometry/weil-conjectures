+++
id = "lemma-nagata-immersion-into-fp-model"
kind = "lemma"
title = "Immersion into a finite-presentation model, [stacks-project]"
order = 383
lean = ["AlgebraicGeometry.Scheme.Hom.exists_isImmersion_locallyOfFinitePresentation"]
uses = ["def-nagata-noetherian-inverse-system", "prop-nagata-noetherian-inverse-system"]
+++
Let $S$ be quasi-compact and quasi-separated and let $f\colon X\to S$ be
quasi-compact and locally of finite type with $X$ quasi-compact and
quasi-separated. Then there exist a scheme $Y$, a morphism $p\colon Y\to S$
of finite presentation, and an immersion $i\colon X\to Y$ over $S$, that is,
with $p\circ i=f$.

## Proof

This is the argument of Tag 01ZE. It uses only a Noetherian approximation of
$X$ itself, not the relative stage data of
[def-nagata-relative-stage-morphism-data].

Write $X=\varprojlim_j X_j$ for a Noetherian approximation of $X$
([prop-nagata-noetherian-inverse-system]): every $X_j$ is of finite type
over $\mathbf Z$ and all transition morphisms, hence also all projections
$\pi_j\colon X\to X_j$, are affine. For an index $k$ put
$Y=X_k\times_{\operatorname{Spec}\mathbf Z}S$ and
$i=(\pi_k,f)\colon X\to Y$, and let $p\colon Y\to S$ be the second
projection. Then $p\circ i=f$, and $p$ is the base change of
$X_k\to\operatorname{Spec}\mathbf Z$, which is of finite presentation because
$X_k$ is of finite type over the Noetherian ring $\mathbf Z$.

It remains to choose $k$ so large that $i$ is an immersion. Cover $X$ by
finitely many affine opens $W_a$ such that $f(W_a)\subseteq V_a$ for affine
opens $V_a\subseteq S$. As $X$ is the limit of the $X_j$, after enlarging the
index we may write $W_a=\pi_j^{-1}(U_a)$ with $U_a\subseteq X_j$ affine open.
Each $\Gamma(W_a)$ is a finitely generated $\Gamma(V_a)$-algebra, and its
finitely many generators are defined at some common stage $k$, that is, they
lie in the image of $\Gamma(U_a^{(k)})\to\Gamma(W_a)$, where $U_a^{(k)}$
denotes the preimage of $U_a$ in $X_k$. Put
$O_a=\mathrm{pr}_1^{-1}(U_a^{(k)})\cap\mathrm{pr}_2^{-1}(V_a)$, an affine open
of $Y$. Then $i^{-1}(O_a)=W_a$, and the map $\Gamma(O_a)\to\Gamma(W_a)$ is
surjective, since its image is a $\Gamma(V_a)$-subalgebra of $\Gamma(W_a)$
containing the chosen generators. So $i$ restricts to a closed immersion
$W_a\to O_a$ for every $a$. The opens $O_a$ cover the image of $i$, and being
an immersion is local on the target, so $i$ is an immersion.
