+++
id = "lem-kun-pullback-constant"
kind = "lemma"
title = "Inverse image of a constant sheaf"
order = 1712
uses = ["def-kun-constant-sheaf", "def-weil-pbc-geometric-stalks", "def-weil-pbc-inverse-image", "lem-kun-stalk-as-pullback", "lemma-weil-pbc-geometric-stalk-conservative"]
+++
For a morphism of schemes $f:X\to Y$ and a $\Lambda$-module (or
complex of $\Lambda$-modules) $M$, the canonical morphism
$f^{-1}\underline{M}\to\underline{M}$ is an isomorphism on
$X_{\Et}$.

## Proof

At a geometric point $\bar x$ of $X$, the
stalk functor is the inverse
image of the point (see [lem-kun-stalk-as-pullback]), so
$(f^{-1}\underline{M})_{\bar x}=(\underline{M})_{f(\bar x)}=M= (\underline{M})_{\bar x}$; the canonical map is an isomorphism on
every stalk hence an isomorphism of sheaves by
[lemma-weil-pbc-geometric-stalk-conservative]; for a complex the
same argument applies degreewise.
