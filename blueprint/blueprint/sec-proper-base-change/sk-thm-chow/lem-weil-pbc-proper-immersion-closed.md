+++
id = "lem-weil-pbc-proper-immersion-closed"
kind = "lemma"
title = "Proper immersions are closed immersions"
order = 1060
uses = ["def-weil-pbc-scheme-conventions", "lem-weil-pbc-proper-closed-image"]
+++
A proper [def-weil-pbc-scheme-conventions] morphism which is an immersion is
a closed immersion, and the image of a proper immersion is closed.

## Proof

Write $f=i\circ j$ with $j:U\hookrightarrow W$ an open immersion and
$i:W\hookrightarrow Y$ a closed immersion, as in the definition of an
immersion of [def-weil-pbc-scheme-conventions]. By
[lem-weil-pbc-proper-closed-image], $f(U)=i(j(U))$ is closed in $Y$, so
$j(U)=i^{-1}(f(U))$ is closed in $W$ as the inverse image of a closed subset
along the closed immersion $i$; being also open in $W$, $j(U)$ is an
open-and-closed subscheme of $W$, and such a subscheme is a closed subscheme
of $W$. Therefore $U\hookrightarrow W\hookrightarrow Y$ is a composite of
closed immersions, so $f$ is a closed immersion, and the image of a proper
immersion is closed by [lem-weil-pbc-proper-closed-image].
