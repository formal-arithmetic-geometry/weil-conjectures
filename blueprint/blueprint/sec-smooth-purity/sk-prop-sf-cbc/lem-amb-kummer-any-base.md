+++
id = "lem-amb-kummer-any-base"
kind = "lemma"
title = "The Kummer sequence on an arbitrary base"
order = 1567
uses = ["def-sc-kummer-sequence", "def-weil-pbc-etale-sheaves"]
+++
Let $n$ be invertible on a scheme $T$. The sequence
of etale sheaves

$$
1\longrightarrow\mu_n\longrightarrow\mathbf G_m
\xrightarrow{z\mapsto z^n}\mathbf G_m\longrightarrow1
$$

is exact. It is the same Kummer sequence as
[def-sc-kummer-sequence], with the curve base replaced
by $T$.

## Proof

The kernel in the sequence of [def-sc-kummer-sequence]
is $\mu_n$ by its equation. To check surjectivity
as an etale sheaf, let $a\in R^\times$ on an affine
etale test object $\operatorname{Spec}R\to T$.
The algebra $R[z]/(z^n-a)$ is free of rank $n$,
and $z$ is a unit in it. The derivative $nz^{n-1}$
is therefore a unit. This algebra defines a finite
etale surjective cover, on which $a$ has the root
$z$. This proves exactness over any base. Pullback
preserves the equations and the root cover, so the
sequence and its connecting maps are natural in $T$.
