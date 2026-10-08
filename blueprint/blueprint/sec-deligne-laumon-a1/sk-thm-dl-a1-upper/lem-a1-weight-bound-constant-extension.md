+++
id = "lem-a1-weight-bound-constant-extension"
kind = "lemma"
title = "Weight bounds over a finite constant-field extension"
order = 2802
uses = ["def-weil-frobenius-module-weights"]
+++
Let $k_0=\mathbf F_q$, let $k'_0=\mathbf F_{q^m}$ be a finite
extension of $k_0$, and let $(V,F)$ be as in
[def-weil-frobenius-module-weights], with the embedding $\iota$
and the prime power $q$ of that definition. Suppose that every
eigenvalue $\lambda$ of $F^m$ satisfies
$|\iota(\lambda)|^2\leq(q^m)^b$. Then every eigenvalue $\alpha$ of
$F$ satisfies $|\iota(\alpha)|^2\leq q^b$: the weight bound for the
target over the extended finite field implies the same bound over the
original field.

## Proof

For an extension of degree $m$, Frobenius becomes $F^m$
and the field cardinality becomes $q^m$, and the eigenvalues of
$F^m$ are the $m$-th powers of those of $F$ in the convention of
[def-weil-frobenius-module-weights].
Thus $|\iota(\alpha^m)|^2=|\iota(\alpha)|^{2m}\leq(q^m)^b=q^{mb}$ is
equivalent to $|\iota(\alpha)|^2\leq q^b$.
