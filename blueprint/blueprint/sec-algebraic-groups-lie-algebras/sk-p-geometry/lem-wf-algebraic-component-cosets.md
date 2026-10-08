+++
id = "lem-wf-algebraic-component-cosets"
kind = "lemma"
title = "Identity component, cosets, and the finite component group"
order = 2494
uses = ["def-wf-algebraic-components", "lem-wf-affine-noetherian-components"]
+++
For a closed algebraic subgroup $H\subseteq\operatorname{GL}(V)$,
the identity component $H^\circ$ is a closed, open, normal subgroup.
The connected components are exactly the pairwise disjoint cosets
$hH^\circ$. There are finitely many of them, and multiplication of
cosets makes

$$
\pi_0(H)=H/H^\circ
$$

a finite group.

## Proof

A finite-type algebraic variety has finitely many irreducible
components ([lem-wf-affine-noetherian-components]). Every connected component is a union of irreducible
components: if an irreducible component meets a connected component,
their union is connected, so maximality of the connected component
contains that irreducible component. Hence there are finitely many
connected components. Each is closed, and its complement, being a
finite union of the other closed components, is closed; thus each
component is also open.

The image of the connected space
$H^\circ\times H^\circ$ under multiplication is connected and
contains the identity. By the definition of $H^\circ$ in
[def-wf-algebraic-components], that image lies in $H^\circ$.
The image of $H^\circ$ under inversion is connected and contains
the identity as well, so it too lies in $H^\circ$. Therefore
$H^\circ$ is a subgroup. Conjugation by any $h\in H$ is a
homeomorphism fixing the identity, so it preserves $H^\circ$;
thus this subgroup is normal.

Translation by $h$ is a homeomorphism and carries $H^\circ$
onto a connected open-and-closed subset containing $h$. It is
therefore exactly the connected component of $h$. The components
are consequently the disjoint cosets $hH^\circ$. Normality makes
coset multiplication well defined, and the already proved finiteness
of the component set makes $H/H^\circ$ a finite group.
