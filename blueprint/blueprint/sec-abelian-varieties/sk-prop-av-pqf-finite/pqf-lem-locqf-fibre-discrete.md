+++
id = "pqf-lem-locqf-fibre-discrete"
kind = "lemma"
title = "Finite fibre over a point"
order = 548
uses = ["def-weil-pbc-scheme-conventions", "pqf-def-quasifinite", "pqf-lem-qf-finitefibres"]
+++
Let $f:X\to S$ be a morphism of schemes and $s\in S$. If $f$ is
locally of finite type and $f^{-1}(\{s\})$ is a finite set, then $X_s$
is a finite discrete space and $f$ is quasi-finite at each point of
$X$ lying over $s$.

## Proof

The fibre $X_s=X\times_S\operatorname{Spec}\kappa(s)$ is locally of
finite type over the field $\kappa(s)$ and has finitely many points;
as in the proof of [pqf-lem-qf-finitefibres], restricting to an
affine open $\operatorname{Spec}A$ over an affine open
$\operatorname{Spec}R\subset S$, the finite type
$\kappa(s)$-algebra $A\otimes_R\kappa(s)$ has finitely many prime
ideals, hence is Artinian, all its primes maximal, and its spectrum is
a finite discrete set. Hence $X_s$ is a finite discrete space, each of
its points is isolated, and at every point the ring map is quasi-finite
at the corresponding prime in the sense of
[pqf-def-quasifinite], i.e. $f$ is quasi-finite at each point
over $s$.
