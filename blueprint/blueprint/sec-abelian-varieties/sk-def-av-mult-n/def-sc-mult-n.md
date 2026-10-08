+++
id = "def-sc-mult-n"
kind = "definition"
title = "Multiplication by $n$ and $n$-torsion"
lean = ["AlgebraicGeometry.torsionSubgroupScheme"]
order = 434
uses = ["def-sc-abelian-variety", "def-sc-group-scheme", "lem-sc-kernel-subgroup"]
+++
Let $A$ be an abelian variety
over $k$ and $n\geq1$. The $n$-th *multiplication map*
$[n]:A\to A$ is the
homomorphism given on points by
$a\mapsto a+\cdots+a$ ($n$ summands). The $n$-*torsion
subgroup scheme* is the kernel

$$
A[n]:=\ker([n]),
$$

a closed subgroup scheme of $A$ ([def-sc-group-scheme], [lem-sc-kernel-subgroup]).
