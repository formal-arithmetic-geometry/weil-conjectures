+++
id = "lemma-nagata-finite-type-to-separated-target"
kind = "lemma"
title = "Finite type over a separated target"
order = 78
lean = ["AlgebraicGeometry.locallyOfFiniteType_of_comp"]
+++
In a commutative triangle $T\to Y\to B$, if $T\to B$ is of finite
type and $Y\to B$ is separated, then $T\to Y$ is of finite type.

## Proof

Factor $T\to Y$ as its graph

$$
T\longrightarrow T\times_BY\longrightarrow Y.
$$

The graph is a closed immersion because $Y\to B$ is separated, hence is
of finite type. The second map is the base change of the finite-type
morphism $T\to B$. Their composite is therefore of finite type.
