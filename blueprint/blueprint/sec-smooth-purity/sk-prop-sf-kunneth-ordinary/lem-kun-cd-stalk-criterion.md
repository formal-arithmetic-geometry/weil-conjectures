+++
id = "lem-kun-cd-stalk-criterion"
kind = "lemma"
title = "Vanishing of a higher direct image, checked at a geometric point"
order = 1655
uses = ["def-weil-pbc-direct-image", "def-weil-pbc-etale-sheaves", "def-weil-pbc-geometric-stalks", "def-weil-pbc-scheme-conventions", "def-weil-pbc-strict-henselization-limit", "lemma-weil-pbc-geometric-stalk-conservative"]
+++
Let $f:X\to Y$ be a
quasi-compact and
quasi-separated morphism of schemes, let $q\ge0$, and let $F$ be a
torsion etale sheaf on
$X_{\Et}$. Then $R^qf_*F=0$ if and only if for every geometric
point $\bar y$ of $Y$ the filtered colimit of the groups
$H^q(W\times_YX,F)$, taken over the
pointed etale
neighbourhoods $(W,\bar w)$ of $\bar y$ (the strict local test
schemes of [def-weil-pbc-strict-henselization-limit]), vanishes.

## Proof

By [def-weil-pbc-direct-image] the sheaf $R^qf_*F$ is the
sheafification of the presheaf $W\mapsto H^q(W\times_YX,F)$ on
$Y_{\Et}$, and by [def-weil-pbc-geometric-stalks] its stalk at
a geometric point $\bar y$ of $Y$ is precisely the filtered colimit
of these groups over the pointed etale neighbourhoods of $\bar y$.
The sheaf $R^qf_*F$ vanishes if and only if all its geometric stalks
vanish, by [lemma-weil-pbc-geometric-stalk-conservative]; hence the
stated equivalence.
