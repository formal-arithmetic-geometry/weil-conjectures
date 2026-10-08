+++
id = "lem-sf-hom-finite-projective"
kind = "lemma"
title = "Internal Hom with a finite projective module"
order = 2082
uses = ["def-sf-datum", "def-weil-derived-pullback-tensor-hom"]
+++
In the setting of [def-sf-datum], let $P$ be a finite projective
$\Lambda_X$-module on the site of $X$, put
$P^\vee=\mathcal H om_X(P,\Lambda_X)$, and let
$N\in D^b_{ctf}(X,\Lambda)$. Then the canonical map
$P^\vee\otimes^L_{\Lambda_X}N\to R\mathcal H om_X(P,N)$ of the
tensor–internal-Hom adjunction is an isomorphism, natural in $P$ and $N$,
and the canonical map $P\to P^{\vee\vee}$ is an isomorphism.

## Proof

For $P=\Lambda_X^r$ finite free the displayed map is the coordinate
identification of $N^{\oplus r}$ with itself and $P\to P^{\vee\vee}$ is the
identity. Both constructions are exact functors of $P$ and preserve direct
summands, a retract being preserved by the internal Hom and by the tensor
product with the canonical maps inherited by the retraction. The assertions
are local on the site and stable under restriction, so they hold for a
general finite projective $P$, which is locally a direct summand of a finite
free module; naturality in $N$ is the naturality of the tensor and
internal-Hom functors of [def-weil-derived-pullback-tensor-hom].
