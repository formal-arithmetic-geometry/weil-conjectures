+++
id = "thm-amb-p1-decomposition"
kind = "theorem"
title = "The projective-line calculation before purity"
order = 1570
uses = ["cor-weil-pbc-geometric-fiber-finite", "def-coefficient-twists-detailed", "def-sc-p1-standard", "def-weil-pbc-derived-categories", "def-weil-pbc-direct-image", "lem-amb-cartier-kummer-map", "lem-amb-proper-coproducts-projection", "lemma-weil-pbc-geometric-stalk-conservative", "thm-sc-proper-cohomology"]
+++
Let $q:P=\mathbf P^1_S\to S$, with $S$ Noetherian.
Let $h$ be the Kummer first Chern class of $\mathcal O_P(1)$.
Then

$$
(1,h):A_S\oplus A_S(-1)[-2]\xrightarrow{\sim}Rq_*A_P
$$

is an isomorphism, compatible with arbitrary change of $S$.
The notation refers to the projective line, Tate twists, ordinary derived categories, and derived direct images.

## Proof

For $\mathbf Z/n$-coefficients, the map is globally
defined by the unit and the Cartier class of infinity in
[lem-amb-cartier-kummer-map]. On a geometric fibre,
[thm-sc-proper-cohomology] gives cohomology only in
degrees $0,2$, each free of rank one; the genus is zero.
In its Kummer description, the degree-two map is
$\operatorname{Pic}(\mathbf P^1)/n\to H^2(\mathbf P^1,\mu_n)$,
and the class of $\mathcal O(1)$, of degree one, generates.
Thus $(1,h)$ is an isomorphism on every geometric fibre.
By [cor-weil-pbc-geometric-fiber-finite], [lemma-weil-pbc-geometric-stalk-conservative]
it is an isomorphism on $S$. Both defining components
commute with base change, so the isomorphism does too. For
general $A$, tensor this isomorphism over $\mathbf Z/n$
with $A$ and use
[lem-amb-proper-coproducts-projection].
