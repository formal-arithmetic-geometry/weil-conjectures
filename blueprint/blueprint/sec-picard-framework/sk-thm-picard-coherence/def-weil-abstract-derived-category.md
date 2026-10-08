+++
id = "def-weil-abstract-derived-category"
kind = "definition"
title = "Derived category of an abelian category"
order = 633
+++
For an abelian category $\mathcal A$, a cochain complex consists of objects
$K^r$, $r\in\mathbf Z$, and differentials $d^r:K^r\to K^{r+1}$ satisfying
$d^{r+1}d^r=0$. Its cohomology is $\ker d^r/\operatorname{im}d^{r-1}$. A
quasi-isomorphism is a morphism of complexes inducing an isomorphism on every
cohomology object. The derived category $D(\mathcal A)$ is the localization
of the category of cochain complexes at these quasi-isomorphisms, with
morphism sizes taken in the chosen universe. See
[Stacks Project, Section 13.11](https://stacks.math.columbia.edu/tag/05RR).
