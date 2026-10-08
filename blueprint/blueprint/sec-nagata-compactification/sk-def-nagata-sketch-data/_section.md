+++
id = "sk-def-nagata-sketch-data"
kind = "section"
title = "Compactification and admissible blow-up"
order = 3
lean = ["AlgebraicGeometry.Compactification", "AlgebraicGeometry.IsSchemeTheoreticallyDominant", "AlgebraicGeometry.IsAdmissible"]
+++
*Definition (sketch).*

A *compactification* of $f:X\to S$ is a factorization

$$
X\xrightarrow{j}\overline X\xrightarrow{p}S,
\qquad p\circ j=f,
$$

where $j$ is a quasi-compact open immersion and $p$ is proper.
It is *scheme-theoretically dense* if
$\mathcal O_{\overline X}\to j_*\mathcal O_X$ is injective.
For a quasi-compact open $U\subseteq T$ in a qcqs scheme, a
*$U$-admissible blow-up* is
$\Bl_{\mathcal I}(T)\to T$, with $\mathcal I$ a finite-type
quasi-coherent ideal satisfying $\mathcal I|_U=\mathcal O_U$.
It is an isomorphism over $U$.
