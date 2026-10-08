+++
id = "lem-a1-punctual-bound-module-mixed"
kind = "lemma"
title = "Punctual bound suffices for a module bound"
order = 2788
uses = ["def-weil-frobenius-module-weights", "lem-a1-spectrum-exact-sequence"]
+++
Let $(V,F)$ be a finite-dimensional $\Qlb$-Frobenius module in the
sense of [def-weil-frobenius-module-weights] such that every
eigenvalue $\alpha$ of $F$ satisfies
$|\iota(\alpha)|\leq q^{w/2}$.
Then $(V,F)$ is $\iota$-mixed of weights at most $w$.

## Proof

Choose a Jordan–Holder filtration of the finite-dimensional module
$(V,F)$. Every nonzero simple Frobenius module is one-dimensional:
after extending scalars (already allowed in $\Qlb$), a simple nonzero
$F$-stable subspace contains an eigenvector, and the span of that
eigenvector is a nonzero stable subspace, hence the whole module. Thus
each graded piece has a single eigenvalue $\lambda$, which is also an
eigenvalue of $F$ by
[lem-a1-spectrum-exact-sequence]; its modulus is at most
$q^{w/2}$. It is therefore $\iota$-pure of weight
$2\log_q|\iota(\lambda)|\le w$ in the sense of
[def-weil-frobenius-module-weights].
Hence the Jordan–Holder filtration exhibits $(V,F)$ as $\iota$-mixed
of weights at most $w$.
