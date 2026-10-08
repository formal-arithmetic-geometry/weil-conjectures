+++
id = "sk-prop-h1"
kind = "section"
title = "$H^1$ via Kummer"
order = 926
uses = ["sk-def-kummer", "sk-def-pic", "sk-prop-kummer-exact"]
+++
*Proposition (sketch).*

For $C$ as in [sk-def-curve] and every $n\ge1$ prime to
$\operatorname{char}k$ there is a canonical short exact sequence

$$
0\to\mathcal O_C(C)^\times/\mathcal O_C(C)^{\times n}\to H^1(C,\mu_n)
\to\Pic(C)[n]\to0 .
$$

In particular $H^1(C,\mu_n)\cong\Pic(C)[n]$ whenever
$\mathcal O_C(C)^\times$ is $n$-divisible, e.g. when $C$ is proper:
then $\mathcal O_C(C)$ is a finite $k$-algebra, whose unit group is a
product of copies of $k^\times$ and of a unipotent group $1+\mathfrak n$
($\mathfrak n$ nilpotent), both $n$-divisible since $k$ is algebraically
closed and $n$ is invertible in $k$.

## Proof

The sequence of [sk-def-kummer] is exact by
[sk-prop-kummer-exact] (here $n$ is prime to
$\operatorname{char}k$), so it has a long exact cohomology sequence,
which reads

$$
\cdots\to\mathcal O_C(C)^\times\xrightarrow{n}\mathcal O_C(C)^\times
\to H^1(C,\mu_n)\to\Pic(C)\xrightarrow{n}\Pic(C)
\to\cdots,
$$

with $H^0(C,\mathbb G_m)=\mathcal O_C(C)^\times$ and
$H^1(C,\mathbb G_m)=\Pic(C)$ by [sk-def-pic]. By exactness, the map
$H^1(C,\mu_n)\to\Pic(C)$ has image $\ker(n)=\Pic(C)[n]$ and kernel the
image of $\mathcal O_C(C)^\times$, which is the cokernel
$\mathcal O_C(C)^\times/\mathcal O_C(C)^{\times n}$ of the $n$-th power map.
This is the short exact sequence; when the $n$-th power map is surjective
its first term vanishes.

Uses: [sk-def-kummer], [sk-def-pic], [sk-prop-kummer-exact]
