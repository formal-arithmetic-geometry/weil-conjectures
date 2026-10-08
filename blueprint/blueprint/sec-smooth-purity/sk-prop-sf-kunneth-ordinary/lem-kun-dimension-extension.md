+++
id = "lem-kun-dimension-extension"
kind = "lemma"
title = "Dimension after extension and restriction"
order = 1729
uses = ["def-kun-dimension", "def-weil-pbc-scheme-conventions", "lem-kun-dimension-formula"]
+++
Let $X$ be a scheme of finite type over a field $K$. For every
field extension $L/K$, one has $\kundim X_L=\kundim X$. If
$U\hookrightarrow X$ is an open dense immersion, then
$\kundim U=\kundim X$.

## Proof

For a scheme of finite type over a field, the dimension formula
[lem-kun-dimension-formula] (applied at the generic points of the
irreducible components, and at all points for the upper bound; Noether
normalization and the additivity of transcendence degree, both basic
commutative algebra) shows that the Krull dimension equals the
supremum of the transcendence degrees $\operatorname{trdeg}_K\kappa(x)$
of its points. Hence an open dense immersion $U\hookrightarrow X$ has
$\kundim U=\kundim X$: the generic points of the irreducible
components of $X$ lie in $U$ because $U$ is dense, and chains of
irreducible closed subsets are computed by the same generic points.
For a field extension $L/K$, each residue field of $X_L$ is a
finitely generated extension of $L$ obtained from a residue field of
$X$ by base change, so its transcendence degree over $L$ is at most
the transcendence degree of the corresponding residue field over $K$
(again additivity of transcendence degree); conversely the projection
$X_L\to X$ is faithfully flat and of finite type, so its fibres are
nonempty and the dimension formula for morphisms gives
$\kundim X_L\ge\kundim X$. Hence $\kundim X_L=\kundim X$.
