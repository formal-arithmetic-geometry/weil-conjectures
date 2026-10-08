+++
id = "lem-sc-mult-n-etale-kernel"
kind = "lemma"
title = "Multiplication by $d$ prime to the characteristic is etale"
order = 588
uses = ["def-sc-abelian-variety", "def-sc-mult-n", "lem-sc-fg-order-prime-etale", "lem-sc-mult-n-finite-flat"]
+++
Let $A$ be an abelian variety of dimension $g$ over a field $k$
and let $d\geq1$. If $\operatorname{char}k\nmid d$, the
kernel $A[d]$ of $[d]:A\to A$ of [def-sc-mult-n] is etale
(equivalently $[d]$ is etale), and $A[d]$ is
etale-covering of the constant group scheme $(\mathbf Z/d\mathbf Z)^{2g}$
([lem-sc-fg-order-prime-etale]).
(*Stacks Project, Groupoid Schemes,
Lemma 39.9.9, [Tag 0BFH](https://stacks.math.columbia.edu/tag/0BFH)*.)

## Proof

By [lem-sc-mult-n-finite-flat], $[d]$ is finite flat with kernel of
order $d^{2g}$. The etaleness of the kernel when $\operatorname{char}k\nmid d$,
and its description as an etale covering of the constant group scheme
$(\mathbf Z/d\mathbf Z)^{2g}$, are Lemma 39.9.9
([Tag 0BFH](https://stacks.math.columbia.edu/tag/0BFH)) together
with [lem-sc-fg-order-prime-etale]; no separate
proof is given.
