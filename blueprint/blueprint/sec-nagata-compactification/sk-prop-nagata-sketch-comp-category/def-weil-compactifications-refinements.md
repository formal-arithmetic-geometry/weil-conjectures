+++
id = "def-weil-compactifications-refinements"
kind = "definition"
title = "Compactifications and refinements"
order = 413
uses = ["def-weil-geometric-hypotheses", "def-weil-scheme-morphism-properties"]
+++
Let $S$ be a scheme; when $S$ is a finite-field scheme, impose the geometric
hypotheses [def-weil-geometric-hypotheses]. Let $X$ and $Y$ be finite-type
[def-weil-scheme-morphism-properties] $S$-schemes, and let $f:X\to Y$ be a
separated finite-type $S$-morphism. A *compactification* $c=(j,\bar f)$ of
$f$ is a factorization

$$
 X\xrightarrow{j}\overline X\xrightarrow{\bar f}Y
$$

with $j$ an open immersion, $\bar f$ a proper $S$-morphism, and $\bar f\circ
j=f$. A *refinement* $u:c_1\to c_2$ is a proper $Y$-morphism

$$
 u:\overline X_1\longrightarrow\overline X_2
$$

such that $u\circ j_1=j_2$. Compactifications and refinements form a category
$\operatorname{Comp}(f)$.
