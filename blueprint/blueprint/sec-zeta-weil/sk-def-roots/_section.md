+++
id = "sk-def-roots"
kind = "section"
title = "Reciprocal roots, weights and integrality"
order = 2858
lean = ["Polynomial.IsPureOfWeight", "Polynomial.IsUniversallyPureOfWeight", "Polynomial.alternatingNatDegreeSum", "shiftSpan"]
+++
*Definition (sketch).*

With $P_i\in\Z[T]$ the integral factor that [sk-thm-intfactors] produces
later (a forward pointer only: nothing here depends on it, and the notions
below are applied to the $\ell$-adic factors $P_{i,\ell}$ wherever they are
used before that theorem) put $b_i=\deg P_i$ and
$P_i^{\#}(U)=U^{b_i}P_i(U^{-1})$. A *reciprocal root* is a root
$\alpha\in\overline{\Q}$ of $P_i^{\#}$, and $\beta=\alpha^{-1}$ is the
corresponding *ordinary root*. Fix an embedding
$\iota:\Qlb\hookrightarrow\C$; a reciprocal root $\alpha$ is a *$q$-Weil
number of weight $i$* if $|\tau(\alpha)|=q^{i/2}$ for every embedding
$\tau:\Q(\alpha)\hookrightarrow\C$. The *Betti numbers* are
$b_i=\deg P_i$, the *determinant constants* are
$D_i=(-1)^{b_i}[T^{b_i}]P_i(T)$, and $\chi=\sum_{i=0}^{2d}(-1)^{i}b_i$.
For $C(T)=\sum_{n\ge0}c_nT^{n}\in K[[T]]$ the *Hankel matrix* is
$\mathcal H(C)=(c_{r+s})_{r,s\ge0}$ and its *Hankel rank* is the rank of
this (possibly infinite) matrix; a *normalized integral presentation* is a
pair $A,B\in\Z[T]$ with $Z=A/B$, $A(0)=B(0)=1$ and $\gcd(A,B)=1$ in $\Q[T]$.
