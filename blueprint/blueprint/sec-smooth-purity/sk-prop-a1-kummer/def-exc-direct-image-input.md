+++
id = "def-exc-direct-image-input"
kind = "definition"
title = "The classical direct-image finiteness input"
order = 1921
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-direct-image", "def-weil-pbc-etale-sheaves", "def-weil-pbc-scheme-conventions"]
+++
Let $k$ be a field, let $N$ be an integer prime to
$\operatorname{char}(k)$, and let $\Lambda$ be a finite commutative
ring annihilated by $N$. Say that the *direct-image finiteness
input over $k$* holds if the following two clauses hold.

1. (*finiteness of the direct image*) For every morphism
$u:S\to T$ of
finite type between
finite-type $k$-schemes, every
constructible
$\Lambda$-sheaf $F$ on
$S_{{\mathrm{et}}}$, and every $q\geq0$, the higher direct image
$R^qu_*F$ of [def-weil-pbc-direct-image] is constructible on
$T_{{\mathrm{et}}}$.
1. (*cohomological dimension*) Let $K$ be a separably closed
field with $\operatorname{char}(K)$ prime to $N$, and let $W$
be a finite-type $K$-scheme of dimension at most $d$. Then
$H^q(W,M)=0$ for every $q>2d$ and every torsion sheaf of abelian
groups $M$ on $W_{{\mathrm{et}}}$.

Both clauses concern the ordinary direct image and the etale cohomology
of schemes only: neither of them mentions the exceptional inverse image,
the ambient exceptional right adjoint datum, purity, or base change. Both
clauses are proved in this blueprint, in the constructibility chapter and the Jacobian chapter
respectively; the classical sources of the two statements, and the way
they are used here, are recorded in the remark that follows.
