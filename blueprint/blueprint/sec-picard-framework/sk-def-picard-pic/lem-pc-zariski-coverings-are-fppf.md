+++
id = "lem-pc-zariski-coverings-are-fppf"
kind = "lemma"
title = "Zariski coverings are fppf coverings"
order = 797
uses = ["def-pc-fppf-site", "def-pc-morphism-conventions", "def-pc-scheme"]
+++
Let $T$ be a scheme and $\{U_i\to T\}_{i\in I}$ a Zariski covering
(each $U_i\to T$ an open immersion, the $U_i$ covering $T$). Then
$\{U_i\to T\}$ is an
fppf covering of $T$.

## Proof

Each $U_i\to T$ is locally of finite presentation (an open immersion
$U\to T$ is, on affine patching of $T$ by $\operatorname{Spec}(A)$ and $U$ by
$\operatorname{Spec}(A_f)$, the map $\operatorname{Spec}(A_f)\to\operatorname{Spec}(A)$; $A_f=A[x]/(fx-1)$ is a
finitely presented $A$-algebra) and flat (the localization $A\to A_f$
is flat: localization is exact). Hence every $U_i\to T$ is flat and
locally of finite presentation, so the family is an fppf covering.
