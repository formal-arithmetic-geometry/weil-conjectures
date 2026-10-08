+++
id = "def-nagata-scheme-theoretically-dense-open"
kind = "definition"
title = "Scheme-theoretically dense open immersion"
order = 6
+++
**Status.** Bypassed by the formalized route: scheme-theoretic density is
the predicate `AlgebraicGeometry.IsSchemeTheoreticallyDominant`,
which [def-nagata-dense-compactification] uses directly.

For a quasi-compact open immersion $j\colon U\hookrightarrow X$, say that
$U$ is scheme-theoretically dense in $X$ if the sheaf morphism

$$
\mathcal O_X\longrightarrow j_*\mathcal O_U
$$

is injective. This predicate is independent of whether the ambient scheme
is presented as part of a compactification.
