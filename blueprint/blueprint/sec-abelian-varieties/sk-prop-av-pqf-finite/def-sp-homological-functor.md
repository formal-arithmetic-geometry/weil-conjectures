+++
id = "def-sp-homological-functor"
kind = "definition"
title = "Homological functors of triangulated categories"
order = 504
uses = ["def-sp-abelian"]
+++
Let $\mathcal C$ be a pretriangulated category (with shift $[1]$,
distinguished triangles and rotation), and let $\mathcal A$ be abelian
[def-sp-abelian]. An additive functor $F:\mathcal C\to\mathcal A$ is
*homological* if for every distinguished triangle $K_1\to K_2\to K_3\to
K_1[1]$ the sequences $F(K_1)\to F(K_2)\to F(K_3)$ and $F(K_3)\to F(K_1[1])$
are exact at the middle spots.
