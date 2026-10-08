+++
id = "lem-pur-etale-iso-descent"
kind = "lemma"
title = "Isomorphisms descend along etale surjections"
order = 1992
uses = ["def-pur-conventions", "def-sbc-smooth-morphisms", "def-weil-derived-cohomology-sheaves", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $u:U\to X$ be a surjective etale morphism of
separated finite-type
$k$-schemes, and let $\varphi:M\to N$ be a morphism of bounded
constructible complexes on $X$. If $Lu^*\varphi$ is an isomorphism,
then $\varphi$ is an isomorphism.

## Proof

It suffices to show that the
[def-weil-derived-cohomology-sheaves] cohomology sheaves
$\mathcal H^r(\varphi)$ are isomorphisms: the geometric fibers of a
surjective etale morphism cover the geometric points of $X$, the
stalks of $Lu^*\varphi$ are the stalks of $\varphi$ at the same
geometric points, and the induced maps on the stalks are isomorphisms;
hence every stalk of every $\mathcal H^r(\varphi)$ is an isomorphism,
so the sheaf morphisms are isomorphisms. The bounded complex case
follows by induction on the interval of nonzero cohomology, using the
exact triangle of the truncations.
