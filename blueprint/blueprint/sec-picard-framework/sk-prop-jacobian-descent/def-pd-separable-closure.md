+++
id = "def-pd-separable-closure"
kind = "definition"
title = "Separable closure"
order = 856
uses = ["def-pc-base-change", "def-pc-separably-closed"]
+++
Let $k$ be a field. A *separable closure* of $k$ is a field $k_s$
together with a $k$-embedding $k\hookrightarrow k_s$ such that $k_s$ is
separably closed and algebraic and
separable over $k$; it is the compositum of the finite separable subextensions
$K/k$ of $k_s$, so that

$$
k_s=\colim_{K/k\ \text{finite separable}}K
$$

as a filtered colimit of $k$-algebras, and $\Spec(k_s)\to\Spec(k)$ is
faithfully flat. We fix one such $k_s$ for each field $k$ and write $C_{k_s}$
for the base change of a $k$-scheme $C$ along
$\Spec(k_s)\to\Spec(k)$.
