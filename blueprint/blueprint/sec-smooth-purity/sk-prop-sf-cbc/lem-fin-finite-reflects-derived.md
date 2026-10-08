+++
id = "lem-fin-finite-reflects-derived"
kind = "lemma"
title = "Finite direct image reflects bounded constructibility"
order = 1627
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-derived-categories", "def-weil-pbc-direct-image", "def-weil-pbc-scheme-conventions", "lem-fin-finite-reflects-constructibility", "lemma-weil-pbc-finite-direct-image-exact", "lemma-weil-pbc-finite-stalk-formula", "lemma-weil-pbc-geometric-stalk-conservative"]
+++
Let $p:Z\to S$ be a
finite morphism of
Noetherian schemes and let $\Lambda$ be a finite commutative ring.
On ordinary derived
categories of etale modules, its
derived direct image $Rp_*$
reflects membership in
$D^b_c$.

## Proof

Exactness from [lemma-weil-pbc-finite-direct-image-exact] gives
$\mathcal H^q(Rp_*K)=p_*\mathcal H^q(K)$.
By [lemma-weil-pbc-finite-stalk-formula], $p_*G=0$ forces
every $G_{\bar z}=0$, and then $G=0$ by
[lemma-weil-pbc-geometric-stalk-conservative].
Thus cohomological bounds on $Rp_*K$ also hold on $K$.
Apply [lem-fin-finite-reflects-constructibility] in each
remaining degree to $G=\mathcal H^q(K)$.
