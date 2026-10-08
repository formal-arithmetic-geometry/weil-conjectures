+++
id = "lem-a1-subquotient-extension-bounds"
kind = "lemma"
title = "Subquotient bounds for Frobenius modules"
order = 2733
uses = ["def-weil-frobenius-module-weights", "lem-a1-spectrum-exact-sequence", "p-linear-filtration"]
+++
If $(V,F)$ is mixed of weights at most $w$, then every
Frobenius-stable subquotient of $V$ is mixed of weights at most $w$.

## Proof

A finite-dimensional
Frobenius module all of whose Frobenius eigenvalues have $\iota$-modulus
at most $q^{w/2}$ is mixed of weights at most $w$: a Jordan–Holder
filtration of the module has graded pieces with eigenvalues among those ([p-linear-filtration])
of the module, hence pure of weights at most $w$, which is the
filtered criterion of [def-weil-frobenius-module-weights]. Every
eigenvalue of the Frobenius on a submodule or on a quotient is an
eigenvalue of the Frobenius on the ambient module (a quotient's
characteristic polynomial divides that of the ambient endomorphism by
[lem-a1-spectrum-exact-sequence], and a submodule's eigenvalues are
eigenvalues by the same triangular matrix argument), so both are mixed
of weights at most $w$.
