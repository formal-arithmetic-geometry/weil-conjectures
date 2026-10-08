+++
id = "lem-pod-perfect-point-complex-field"
kind = "lemma"
title = "Perfect point complexes over a field"
order = 2413
uses = ["def-pod-conventions", "def-pod-perfect-point-complex", "def-weil-finite-coefficient-point"]
+++
In the Poincare duality conventions of
this chapter, suppose that the coefficient ring $A$ of the
category at the point is a
field, and let $C$ be an object of that category. Then $C$ is
perfect if and only if $C$ is
bounded and all its cohomology groups $H^i(C)$ are finite dimensional
over $A$.

## Proof

Over a field every complex of $A$-modules is quasi-isomorphic to the
direct sum of the shifts of its cohomology,
$\bigoplus_iH^i(C)[-i]$: this is the classical splitting of a complex
of vector spaces, obtained by choosing splittings of the surjections
$Z^i(C)\twoheadrightarrow H^i(C)$ and of the inclusions
$Z^i(C)\hookrightarrow C^i$, which exist because every short exact
sequence of vector spaces splits. If $C$ is bounded with
finite-dimensional cohomology, that quasi-isomorphism exhibits $C$ as a
bounded complex of finite projective $A$-modules, so $C$ is perfect
in the sense of [def-pod-perfect-point-complex]. Conversely, if
$C$ is quasi-isomorphic to a bounded complex $P$ of finite projective
$A$-modules, then $H^i(C)\cong H^i(P)$ is a quotient of the
finite-dimensional $A$-module $P^i$, hence finite dimensional, and
vanishes outside the finite range in which $P$ is concentrated; so
$C$ is bounded with finite-dimensional cohomology. This proves both
implications.
