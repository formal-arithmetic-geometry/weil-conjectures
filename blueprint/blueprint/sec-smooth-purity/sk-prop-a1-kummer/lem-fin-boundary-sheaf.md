+++
id = "lem-fin-boundary-sheaf"
kind = "lemma"
title = "Boundary sheaf of an open immersion"
order = 1910
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-inverse-image", "def-weil-pbc-scheme-conventions", "sbc-def-coefficient-conventions", "thm-fin-open-degree-zero"]
+++
Let $X$ be of finite type over $k$, let $j:U\hookrightarrow X$ be an
open immersion, let
$i:Z=X\setminus U\hookrightarrow X$ be its closed complement, and let
$F$ be a constructible
$\Lambda$-sheaf on $U_{{\mathrm{et}}}$. Then the boundary sheaf
$i^*j_*F$, with the inverse image of
[def-weil-pbc-inverse-image], is constructible on $Z_{{\mathrm{et}}}$.

## Proof

By [thm-fin-open-degree-zero], the sheaf $j_*F$ is
constructible. Pull back its finite locally closed partition
and the finite constant etale trivializations on its parts to
$Z$. The inverse image of
[def-weil-pbc-inverse-image] takes a constant finite module
to the same constant module and commutes with restriction.
The pulled-back partition therefore proves constructibility of
$i^*j_*F$, as defined in
[def-weil-pbc-constructible-complexes]. No surjectivity of
restriction maps between punctured neighbourhoods is needed.
