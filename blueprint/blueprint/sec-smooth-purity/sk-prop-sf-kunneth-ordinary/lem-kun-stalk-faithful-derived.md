+++
id = "lem-kun-stalk-faithful-derived"
kind = "lemma"
title = "Stalk faithfulness for derived objects"
order = 1703
uses = ["def-weil-pbc-derived-categories", "lem-kun-d-zero-cohomology", "lem-kun-stalk-as-pullback", "lem-kun-stalks-of-cohomology", "lemma-weil-pbc-geometric-stalk-conservative"]
+++
A morphism in $D(T_{\Et})$ is an isomorphism if and only if its
pullback to every geometric point of $T$ is an isomorphism.

## Proof

Let $\alpha:K\to L$. The cone $C$ of $\alpha$ is zero if and only
if $\alpha$ is an isomorphism; $\mathcal H^q(C)=0$ for all $q$
iff $C=0$ by [lem-kun-d-zero-cohomology]. By
[lem-kun-stalks-of-cohomology] and
[lem-kun-stalk-as-pullback] the stalk of $\mathcal H^q(C)$ at
$\bar t$ is $\mathcal H^q(C_{\bar t})$, and
[lemma-weil-pbc-geometric-stalk-conservative] detects vanishing of
sheaves on their stalks, so $C=0$ iff $C_{\bar t}=0$ for all
$\bar t$, i.e. iff the pullbacks of $\alpha$ are isomorphisms.
