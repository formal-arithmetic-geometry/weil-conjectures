+++
id = "lem-kun-tor-cokernel-flat"
kind = "lemma"
title = "Flatness criterion for a cokernel"
order = 1715
uses = ["def-kun-derived-tensor", "def-weil-pbc-etale-sheaves"]
+++
Let $\Lambda$ be a commutative ring, $T$ a scheme,
$\mathcal K^\bullet$ a complex of flat $\Lambda_T$-module sheaves,
and $a\in\mathbf Z$. Assume that
$H^n(\mathcal K^\bullet\otimes_\Lambda\mathcal M)=0$ for every
$\Lambda_T$-module sheaf $\mathcal M$ placed in degree $0$ and
every $n<a$. Then
$\mathcal N=\operatorname{coker}(\mathcal K^{a-1}\to\mathcal K^a)$
is a flat $\Lambda_T$-module sheaf.

## Proof

The K-flatness and truncation conventions are those of
[def-kun-derived-tensor], and sheaves are understood in the sense
of [def-weil-pbc-etale-sheaves]. A $\Lambda_T$-module sheaf is flat if and only if all its geometric
stalks are flat $\Lambda$-modules, since the stalk functors are
exact, and a $\Lambda$-module $N$ is flat if and only if
$\operatorname{Tor}_1^\Lambda(N,M)=0$ for every $\Lambda$-module
$M$. Fix $\mathcal M$. The sequence
$\mathcal K^{a-1}\to\mathcal K^a\to\mathcal N\to0$ is exact, and its
terms are flat, so it remains exact after tensoring with $\mathcal M$; the exact sequence
$\mathcal K^{a-2}\to\mathcal K^{a-1}\to\mathcal K^a\to\mathcal N\to0$ therefore exhibits

$$
\operatorname{Tor}_1^\Lambda(\mathcal N,\mathcal M)
=\frac{\ker\bigl(\mathcal K^{a-1}\otimes_\Lambda\mathcal
M\to\mathcal K^a\otimes_\Lambda\mathcal M\bigr)}
{\operatorname{im}\bigl(\mathcal K^{a-2}\otimes_\Lambda\mathcal
M\to\mathcal K^{a-1}\otimes_\Lambda\mathcal M\bigr)}
=H^{a-1}\bigl(\mathcal K^\bullet\otimes_\Lambda\mathcal M\bigr),
$$

which vanishes by hypothesis. Hence all Tor groups vanish and
$\mathcal N$ is flat, stalk by stalk.
