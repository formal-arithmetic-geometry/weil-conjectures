+++
id = "lemma-nagata-proper-to-separated-target"
kind = "lemma"
title = "[stacks-project]"
order = 237
lean = ["AlgebraicGeometry.IsProper.of_comp"]
+++
In a commutative triangle $T\to Y\to B$, if $T\to B$ is proper and
$Y\to B$ is separated, then $T\to Y$ is proper.

## Proof

Factor $T\to Y$ through the graph
$T\to T\times_BY$. The graph is closed because $Y\to B$ is separated, and
the projection $T\times_BY\to Y$ is the base change of the proper morphism
$T\to B$.
