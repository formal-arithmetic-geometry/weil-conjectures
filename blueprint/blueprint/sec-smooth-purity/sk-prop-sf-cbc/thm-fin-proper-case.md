+++
id = "thm-fin-proper-case"
kind = "theorem"
title = "The proper case: direct images of proper morphisms"
order = 1623
uses = ["cor-weil-pbc-geometric-fiber-finite", "def-weil-pbc-constructible-complexes", "def-weil-pbc-direct-image", "def-weil-pbc-scheme-conventions", "fin4-lem-fibrewise-cohomological-dimension", "lemma-weil-pbc-geometric-stalk-conservative", "thm-fin-proper-constructibility-complete"]
+++
Let $f:X\to S$ be a proper
morphism with $S$ of finite type over $k$, all
geometric fibres of $f$
of dimension at most $d\in\mathbf Z_{\geq0}$, and let $F$ be a
constructible
$\Lambda$-sheaf on $X_{{\mathrm{et}}}$. Then $R^qf_*F$ of
[def-weil-pbc-direct-image] is constructible on $S_{{\mathrm{et}}}$
for every $q\geq0$, and $R^qf_*F=0$ for $q>2d$.

## Proof

Constructibility follows from
[thm-fin-proper-constructibility-complete], applied to the given
proper morphism and constructible coefficient sheaf.
For every geometric point $\bar s$, proper base change
[cor-weil-pbc-geometric-fiber-finite] identifies

$$
(R^qf_*F)_{\bar s}=H^q(X_{\bar s},F|_{X_{\bar s}}).
$$

The right side is zero above twice the specified fibre-dimension
bound by [fin4-lem-fibrewise-cohomological-dimension].
Geometric stalk conservativity
[lemma-weil-pbc-geometric-stalk-conservative] proves the sheaf vanishing.
Each fibre group is finite because constructible sheaves have finite
stalks by [def-weil-pbc-constructible-complexes].
The constructibility proof uses finite resolutions and proper
modifications; the sharp bound is obtained separately from this
geometric-fibre calculation.
