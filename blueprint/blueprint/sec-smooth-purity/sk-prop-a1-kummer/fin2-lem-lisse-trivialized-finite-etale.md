+++
id = "fin2-lem-lisse-trivialized-finite-etale"
kind = "lemma"
title = "Finite etale trivialization of a lisse sheaf"
order = 1904
uses = ["cor-galois-open-subgroups", "def-weil-pbc-constructible-complexes", "def-weil-pbc-scheme-conventions", "thm-galois-fundamental", "thm-galois-lc-etale"]
+++
Let $X$ be of finite type over a field, let $\Lambda$ be
a finite commutative ring, and let $L$ be a
finite locally
constant $\Lambda$-module sheaf. There is a
finite etale
surjective map $p:P\to X$ such that $p^*L$ is constant
on each connected component of $P$, with a finite
$\Lambda$-module fibre. If $X$ is connected, one common
finite module can be used on all of $P$.

## Proof

A Noetherian scheme has finitely many connected components,
which are open and closed. We may therefore work on a
connected component of $X$. Let $M$ be a geometric
fibre of $L$, finite by
[def-weil-pbc-constructible-complexes]. Apply
[thm-galois-lc-etale], [thm-galois-fundamental] to its
underlying finite locally constant set sheaf and retain
the addition and scalar-multiplication maps. These maps
are preserved by the equivalence, so the resulting action
on $M$ is $\Lambda$-linear. Its kernel in the
profinite fundamental group is open: it is the intersection
of the stabilizers of the finitely many elements of $M$.
The finite cover corresponding to this kernel exists by
[cor-galois-open-subgroups]. On that cover the action
is trivial, so the pulled-back module sheaf is
$\underline M$. This also shows surjectivity of the cover;
its fibres are the nonempty finite coset set.
Take the disjoint union of the covers on the finitely many
connected components. This is finite etale in the sense of
[def-weil-pbc-scheme-conventions], hence of finite type
over the ground field. No freeness assertion about $M$
is used; for instance $\mathbf Z/\ell$ is a finite
$\mathbf Z/\ell^2$-module that is not free.
