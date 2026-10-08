+++
id = "def-nagata-dense-compactification"
kind = "definition"
title = "Scheme-theoretically dense compactification"
order = 7
lean = ["AlgebraicGeometry.IsSchemeTheoreticallyDominant"]
uses = ["def-nagata-compactification", "def-nagata-scheme-theoretically-dense-open"]
+++
A compactification $X\xrightarrow{j}\overline X\to S$ is
*scheme-theoretically dense* when its first map has the predicate
introduced in [def-nagata-scheme-theoretically-dense-open]; explicitly,
this means that

$$
\mathcal O_{\overline X}\longrightarrow j_*\mathcal O_X
$$

is injective.
