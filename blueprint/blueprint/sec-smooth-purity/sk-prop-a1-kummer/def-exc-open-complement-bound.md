+++
id = "def-exc-open-complement-bound"
kind = "definition"
title = "Open-complement cohomological-dimension condition"
order = 1914
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-direct-image", "def-weil-pbc-etale-sheaves", "def-weil-pbc-scheme-conventions", "lem-exc-closed-amplitude", "prop-exc-closed-tor"]
+++
Let $A$ be a finite ring, let $j:V\hookrightarrow T$ be a
quasi-compact open immersion,
and let $c\in\mathbf Z_{\geq0}$. Say that the pair $(V,T)$
satisfies the *open-complement condition with constant $c$* if

$$
R^qj_*M=0\qquad(q>c)
$$

for every sheaf $M$ of $A$-modules on $V_{\mathrm{et}}$, and if
$R^qj_*$ carries constructible
sheaves to constructible sheaves in
every degree. This is exactly the hypothesis under which the closed-support
computations of [lem-exc-closed-amplitude] and
[prop-exc-closed-tor] run: those two statements are conditional on the
open-complement condition for the complement of the closed immersion they
treat, and are unconditional where that condition is known independently,
in dimension at most one and, for the chart complements, from the
classical direct-image finiteness input.
