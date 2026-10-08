+++
id = "lem-kun-support-geometric-point-independent"
kind = "lemma"
title = "The support does not depend on the chosen geometric point"
order = 1678
uses = ["def-kun-support", "def-weil-pbc-geometric-stalks", "def-weil-pbc-inverse-image", "lem-kun-stalk-as-pullback"]
+++
Let $X$ be a scheme, $x\in X$, and let $\bar x,\bar x'$ be
geometric points of $X$ with image $x$. For every etale sheaf
$F$ on $X_{\Et}$ one has $F_{\bar x}=0$ if and only if
$F_{\bar x'}=0$; consequently the
support of $F$ is independent of the
chosen geometric point over each of its points.

## Proof

Write $i:\Spec\kappa(x)\to X$ for the canonical point of $x$. Both
$\bar x$ and $\bar x'$ factor through $i$, say
$\bar x=a\circ i$ and $\bar x'=a'\circ i$, where $a$ and $a'$
are the structure maps of the separably closed extensions
$\Omega/\kappa(x)$ and $\Omega'/\kappa(x)$. By
[lem-kun-stalk-as-pullback] the stalks are the inverse images
along $\bar x$ and $\bar x'$, and inverse images compose
([def-weil-pbc-inverse-image]), so $F_{\bar x}=a^{-1}(i^{-1}F)$
and $F_{\bar x'}=(a')^{-1}(i^{-1}F)$. By
[def-weil-pbc-geometric-stalks] both are filtered colimits of the
sections of $i^{-1}F$ over the pointed etale neighbourhoods of the
respective geometric point, that is, over the finite separable
extensions of $\kappa(x)$ that embed into $\Omega$, respectively
into $\Omega'$; and every finite separable extension of $\kappa(x)$
embeds into either field, both being separably closed. The two
colimits therefore have the same index category up to cofinality and
vanish simultaneously, which gives the first assertion, and with it the
independence, in the sense of [def-kun-support], of the
support of the choice of geometric point.
