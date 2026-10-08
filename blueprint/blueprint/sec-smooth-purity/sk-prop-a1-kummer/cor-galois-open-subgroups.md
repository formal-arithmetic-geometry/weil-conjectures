+++
id = "cor-galois-open-subgroups"
kind = "theorem"
title = "Open subgroups and finite etale covers"
order = 1902
tags = ["latex:corollary"]
uses = ["def-galois-fibre-functor", "def-galois-object", "lem-galois-transitive", "thm-galois-fundamental"]
+++
Let $Y$ be connected with geometric point $\bar y$. Assigning to a
connected finite etale cover $P$ the stabilizer in $\pi_1(Y,\bar y)$ of a
point of $P_{\bar y}$ is a bijection between the isomorphism classes of
connected finite etale covers of $Y$ and the open subgroups of
$\pi_1(Y,\bar y)$, and the degree of $P$ over $Y$ is the index of the
subgroup. (This is the form used without citation in the proof of the
finite-monodromy lemma of the smooth base change chapter.)

## Proof

Here $\pi_1=\pi_1(Y,\bar y)=\operatorname{Aut}(F_{\bar y})$ is the group
of [def-galois-fibre-functor] and the covers are the finite etale
covers of [def-galois-object]. Under [thm-galois-fundamental] connected finite etale covers of $Y$
correspond to transitive finite continuous $\pi_1$-sets — the
transitivity being that of [lem-galois-transitive] — i.e. to
$\pi_1/H$ with $H$ open: the stabilizer of a point of $P_{\bar y}$ is
that subgroup, and $\#F_{\bar y}(P)=\#\pi_1/H=[\pi_1:H]$ is the degree. A
morphism of connected covers corresponds to an equivariant map
$\pi_1/H\to\pi_1/H'$, which exists exactly when $H'$ is contained in
$H$ up to conjugacy, so the assignment is bijective on isomorphism
classes.
