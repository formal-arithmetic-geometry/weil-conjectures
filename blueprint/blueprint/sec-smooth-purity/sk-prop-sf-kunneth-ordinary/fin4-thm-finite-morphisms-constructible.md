+++
id = "fin4-thm-finite-morphisms-constructible"
kind = "theorem"
title = "Finite morphisms preserve constructibility"
order = 1773
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-direct-image", "def-weil-pbc-scheme-conventions", "lem-fin-finite-morphism", "sbc-def-coefficient-conventions"]
+++
Let $f:X\to S$ be a finite
morphism with $S$ of finite type over $k$, and let $F$ be a
constructible
$\Lambda$-sheaf on $X_{{\mathrm{et}}}$ (the ring $\Lambda$ of
[sbc-def-coefficient-conventions]). Then the higher direct
images $R^qf_*F$ of [def-weil-pbc-direct-image] are
constructible on
$S_{{\mathrm{et}}}$ for every $q\geq0$, and $R^qf_*F=0$ for $q>0$:
the vanishing bound $2\cdot0$ of the zero relative dimension.

## Proof

Apply [lem-fin-finite-morphism], which proves both
constructibility of $f_*F$ and exactness of finite direct image.
It uses the finite-stalk formula and the earlier finite-image
constructibility proof, with no cardinality or general finiteness input.
