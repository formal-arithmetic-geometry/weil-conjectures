+++
id = "prop-weil-pbc-kinjective-resolutions-exist"
kind = "theorem"
title = "Existence of K-injective resolutions"
order = 988
uses = ["def-weil-pbc-derived-categories", "def-weil-pbc-etale-sheaves", "def-weil-pbc-kinjective-resolutions"]
tags = ["latex:proposition"]
+++
Every complex in $\mathsf{Cpx}(\Mod(T_{\Et},R))$ admits a K-injective
resolution $K\to I$, functorially up to chain homotopy; two K-injective
resolutions of one object are chain-homotopy equivalent, and a bounded-below
complex of injective objects is K-injective.

## Proof

The category of [def-weil-pbc-etale-sheaves] is Grothendieck abelian; the
existence of a K-injective resolution of every complex, functorially up to
chain homotopy, and the chain-homotopy equivalence of any two K-injective
resolutions of the same object are the theorem on K-injective complexes in
Grothendieck abelian categories (Stacks Project,
[Theorem 19.12.6, Tag 079P](https://stacks.math.columbia.edu/tag/079P)) in
the formulation of [def-weil-pbc-kinjective-resolutions]. A bounded-below
complex $I$ of injective objects is K-injective: for $A$ acyclic, the
spectral sequence of the double complex
$\operatorname{Hom}(A^\bullet,I^\bullet)$ has the
$\operatorname{Hom}(A^\bullet,I^q)$ rows acyclic, since
$\operatorname{Hom}(-,I^q)$ is exact as $I^q$ is injective and $A$ is
acyclic, so $\operatorname{Hom}(A,I)$ is acyclic.
