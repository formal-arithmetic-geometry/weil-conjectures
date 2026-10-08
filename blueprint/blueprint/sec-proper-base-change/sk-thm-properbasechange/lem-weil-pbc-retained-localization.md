+++
id = "lem-weil-pbc-retained-localization"
kind = "lemma"
title = "Properties of the retained localization"
order = 1225
uses = ["def-weil-pbc-ind-etale-algebra", "def-weil-pbc-retained-localization", "def-weil-pbc-w-local", "lem-weil-pbc-ind-etale-stability", "lem-weil-pbc-w-local-partition", "lem-weil-pbc-w-localization-points"]
+++
The map $R\to R_{[T]}$ is ind-Zariski [def-weil-pbc-ind-etale-algebra], and
its points are the pairs $(x,y)$ with $x\in T$, $y\subset x$, with local ring
$R_y$. If all points of $T$ are closed in $\operatorname{Spec}R$, then
$\operatorname{Spec}R_{[T]}$ is w-local [def-weil-pbc-w-local] with closed
point set $T$. If moreover $T=V(J)$, its quotient by $J$ is canonically
$R/J$.

## Proof

The construction in [def-weil-pbc-retained-localization] is a filtered
sequence of idempotent localizations. Such localizations are ind-Zariski, so
[lem-weil-pbc-ind-etale-stability] proves the first assertion. A closed
subset is patch closed. Compactness in
[lem-weil-pbc-w-local-partition] says that the intersection of its
constructible neighbourhoods is exactly itself. Thus
[lem-weil-pbc-w-localization-points] gives precisely the listed pairs and
local rings. The same fibre calculation gives the components
$\operatorname{Spec}R_x$; their closed points $(x,x)$ form the closed subset
obtained by base change from the closed point subset of
$\operatorname{Spec}R^w$.

If $T=V(J)$ consists of maximal ideals, a prime of $R_{[T]}/JR_{[T]}$ has
$J\subset y\subset x$ with $x\in T$. Maximality of every prime containing $J$
forces $y=x$. Both spectra in the quotient map are zero-dimensional affine
spectra, hence compact Hausdorff, and the map is a continuous bijection,
hence a homeomorphism. At every prime the map on local rings is the identity
of $R_x/JR_x$. It is therefore an isomorphism of locally ringed spaces, and
the asserted ring isomorphism follows.
