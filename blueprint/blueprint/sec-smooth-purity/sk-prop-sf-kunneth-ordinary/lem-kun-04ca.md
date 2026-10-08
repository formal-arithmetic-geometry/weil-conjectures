+++
id = "lem-kun-04ca"
kind = "lemma"
title = "Pushforward along a closed immersion"
order = 1693
uses = ["def-kun-support", "def-weil-pbc-direct-image", "def-weil-pbc-geometric-stalks", "def-weil-pbc-inverse-image", "def-weil-pbc-scheme-conventions", "lemma-openclosed-stalk-lowerstar", "lemma-weil-pbc-geometric-stalk-conservative", "prop-openclosed-lowerstar-fully-faithful"]
+++
Let $i:Z\to X$ be a
closed immersion of
schemes. The functor $i_*:\Ab(Z_{\Et})\to\Ab(X_{\Et})$ of
[def-weil-pbc-direct-image] is fully faithful, $i^{-1}$ is a
left inverse, and the essential image consists of those abelian sheaves
on $X_{\Et}$ whose
support is contained in $Z$.

## Proof

For an etale $V\to X$ one has $(i_*F)(V)=F(V\times_XZ)$ by
[def-weil-pbc-direct-image]; for an etale $V\to Z$ the composite
$V\to Z\to X$ is etale and $V\times_XZ=V$, so the restriction of
$i_*F$ to $Z_{\Et}$ is $F$, i.e. $i^{-1}i_*=\mathrm{id}$ by [def-weil-pbc-inverse-image]; in
particular $i_*$ is fully faithful ([prop-openclosed-lowerstar-fully-faithful]).
For the essential image, let $F$ be a sheaf on $X_{\Et}$ with
$\kunsupp F\subseteq Z$ and consider the canonical map
$F\to i_*i^{-1}F$. At a geometric point $\bar x$ of $X$ with
$x\in Z$, the pointed etale neighbourhoods $W\to X$ of $\bar x$
have $W\times_XZ$ cofinal among the pointed etale neighbourhoods of
$\bar x$ in $Z$ by [lemma-openclosed-stalk-lowerstar] (an etale neighbourhood of $\bar x$ in $Z$
extends to one in $X$ by composing with $i$), so
$(i_*i^{-1}F)_{\bar x}=F_{\bar x}$ by
[def-weil-pbc-geometric-stalks]; at a geometric point with
$x\notin Z$, the open complement $X\setminus Z$ provides cofinal
neighbourhoods $W\subseteq X\setminus Z$ with $W\times_XZ=\emptyset$,
so both stalks vanish (for $F$ this is the support hypothesis).
Hence $F\to i_*i^{-1}F$ is an isomorphism on every geometric stalk,
and therefore an isomorphism by
lem:weil-pbc-geometric-stalk-conservative.
