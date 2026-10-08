+++
id = "lem-sc-group-cd-one"
kind = "lemma"
title = "A degree-two criterion for continuous cohomology"
order = 979
uses = ["def-exc-continuous-cohomology", "lem-sc-sylow-module-filtration"]
+++
Let $G$ be profinite and $\ell$ prime. Suppose that
$H^2(H,\mathbf F_\ell)=0$ for every open subgroup $H\subset G$,
with trivial coefficients. Then
$H^q(G,M)=0$ for $q\geq2$ and every discrete continuous
$\ell$-primary module $M$, with cohomology as in
[def-exc-continuous-cohomology].

## Proof

For finite $M$, apply [lem-sc-sylow-module-filtration].
The long exact cohomology sequence, one filtration step at a time,
gives $H^2(H,M)=0$. Restriction followed by corestriction on
$H^2(G,M)$ is multiplication by $[G:H]$. This follows from
the coset-sum formula for corestriction on the continuous cochains
of [def-exc-continuous-cohomology]; conjugation by an element
of $G$ induces the identity on its cohomology. As the index
is prime to $\ell$, multiplication by it is invertible on an
$\ell$-primary group. Hence $H^2(G,M)=0$.

An arbitrary discrete $\ell$-primary module is the directed union
of its finite $G$-stable submodules. Indeed the orbit of each
element is finite, and a finite set of finite-order generators
generates a finite abelian group. A continuous cochain on the
compact space $G^q$ has finite image, so it is contained in one
such submodule. Thus continuous cochain complexes, and their
cohomology, commute with this union. This proves $H^2(G,M)=0$
without a finiteness assumption.

Finally embed $M$ equivariantly in the coinduced module
$\operatorname{Cont}(G,M)$ by $m\mapsto(g\mapsto gm)$, with
right translation on the functions. This is a discrete
$\ell$-primary module. The continuous cochain complex of a
coinduced module is contractible in positive degrees: in homogeneous
cochains the contraction inserts the function argument as the
first group argument. Its cokernel is again discrete
$\ell$-primary. The long exact sequence therefore identifies
$H^{q+1}(G,M)$ with $H^q(G,\operatorname{coker})$ for $q\geq1$.
Repeated dimension shifting reduces every degree at least two
to the vanishing of $H^2$ just proved.
