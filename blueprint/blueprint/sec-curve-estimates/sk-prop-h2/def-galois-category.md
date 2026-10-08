+++
id = "def-galois-category"
kind = "definition"
title = "Galois category"
order = 967
uses = ["def-galois-fibre-functor"]
+++
Let $\mathcal C$ be a category and $F:\mathcal C\to\mathbf{Sets}$ a
functor. The pair $(\mathcal C,F)$ is a *Galois category* if

1. $\mathcal C$ has finite limits and finite colimits;
1. every object of $\mathcal C$ is a finite coproduct of
*connected* objects, where $X$ is connected if it is not initial and
every monomorphism $Y\to X$ is either an isomorphism or has initial
source;
1. $F(X)$ is finite for every object $X$;
1. $F$ is exact (it commutes with finite limits and finite colimits)
and reflects isomorphisms (if $F(f)$ is bijective then $f$ is an
isomorphism).

For a functor with all $F(X)$ finite, $\operatorname{Aut}(F)$ is
identified with the subgroup of
$\prod_X\operatorname{Aut}(F(X))$ formed by the tuples induced by the
natural automorphisms of $F$, and carries the topology induced from the
product of the discrete topologies;
