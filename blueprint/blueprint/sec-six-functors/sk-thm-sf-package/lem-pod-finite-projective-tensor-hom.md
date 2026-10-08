+++
id = "lem-pod-finite-projective-tensor-hom"
kind = "lemma"
title = "Internal Hom with a finite projective module"
order = 2244
uses = ["def-pod-conventions", "def-weil-derived-pullback-tensor-hom", "def-weil-derived-tensor", "def-weil-geometric-hypotheses", "def-weil-pbc-proetale-site"]
+++
In the Poincare duality conventions of this chapter (the fixed setting),
$P$ be a finite projective $\Lambda_X$-module on the
small pro-etale site of $X$,
put $P^\vee=\mathcal Hom_X(P,\Lambda_X)$, and let
$N\in D^b_{ctf}(X,\Lambda)$. The canonical map

$$
P^\vee\otimes^L_{\Lambda_X}N\longrightarrow R\mathcal Hom_X(P,N),
$$

of the tensor–internal-Hom adjunction is an isomorphism, natural in
$P$ and $N$; and the canonical map $P\to P^{\vee\vee}$ is an
isomorphism of $\Lambda_X$-modules.

## Proof

For $P=\Lambda_X^r$ finite free the displayed map is the coordinate
identification of $N^{\oplus r}$ with itself, and $P\to P^{\vee\vee}$
is the identity; both constructions are exact functors of $P$ and
preserve direct summands (a retract is preserved by the internal Hom
and the tensor product, with the canonical maps inherited by the
retraction), by [def-weil-derived-pullback-tensor-hom] and
[def-weil-derived-tensor]. The assertions are local on the site
and stable under restriction, so the general finite projective $P$,
being locally a direct summand of a finite free module, satisfies them.
The naturality in $N$ is the naturality of the tensor and
internal-Hom functors of [def-weil-derived-pullback-tensor-hom].
