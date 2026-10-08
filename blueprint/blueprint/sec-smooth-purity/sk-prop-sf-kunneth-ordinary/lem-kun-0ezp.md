+++
id = "lem-kun-0ezp"
kind = "lemma"
title = "Cohomology of a separably closed field vanishes in positive degrees"
order = 1761
uses = ["def-kun-separably-closed", "def-weil-pbc-direct-image", "def-weil-pbc-etale-cohomology", "def-weil-pbc-etale-sheaves", "def-weil-pbc-etale-site"]
+++
Let $L$ be a
separably closed field and
$X=\Spec(L)$. Then every object of the small etale site of $X$ is a
disjoint union of copies of $X$, and for every abelian sheaf $F$ on
$X_{\Et}$,

$$
H^q(X_{\Et},F)=0\qquad(q>0).
$$

Consequently, for every morphism $f:X\to Y$ of schemes, the higher
direct images of [def-weil-pbc-direct-image] vanish:
$R^qf_*F=0$ for $q>0$.
(*Source:* this is the case of Stacks Project, Tag
[0EZP](https://stacks.math.columbia.edu/tag/0EZP) that is used in this
chapter, namely the case of the spectrum of a separably closed field; the
general statement of that tag, for an integral normal scheme with separably
closed function field, is not needed here.)

## Proof

*Step 1 (etale $L$-schemes).* An etale morphism is locally of finite
presentation, so an etale $L$-scheme is a disjoint union of affine pieces
which are etale and of finite presentation over $L$, hence etale and of
finite type. An etale finite type scheme over a field is finite over that
field, and a finite etale algebra over a field is a product of finite
separable field extensions; since $L$ is separably closed
([def-kun-separably-closed]) each of those extensions is $L$ itself.
Hence every object of the small etale site of $X$,
[def-weil-pbc-etale-site], is a disjoint
union of copies of $X$.

*Step 2 (the global sections functor is exact).* By Step 1 every object
of $X_{\Et}$ is a coproduct of copies of the terminal object $X$, and for
a coproduct the sheaf axiom gives
$F(\coprod_jX)\cong\prod_jF(X)$ for a sheaf $F$ of
[def-weil-pbc-etale-sheaves]. In particular every covering of $X$
contains a summand mapping isomorphically onto $X$, so a section of a
quotient sheaf admits a lift over $X$: the global sections functor
$\Gamma(X_{\Et},-)$ is evaluation at $X$, and the exactness of the
sequence of sheaves gives exactness after evaluation. Hence
$\Gamma(X_{\Et},-)$ is exact, and its derived functors of
[def-weil-pbc-etale-cohomology] vanish in positive degrees.

*Step 3 (higher direct images).* Let $U\to Y$ be etale. Then
$X\times_YU\to X$ is etale (base change of an etale morphism), so it is a
disjoint union of copies of $X$ by Step 1, and

$$
H^q\bigl((X\times_YU)_{\Et},F\bigr)
=\prod\nolimits_jH^q(X_{\Et},F)=0\qquad(q>0)
$$

by Step 2, cohomology of a disjoint union being the product of the
cohomologies. Hence the presheaf $U\mapsto H^q(X\times_YU,F)$ vanishes for
$q>0$, and therefore so does its sheafification, which is
$R^qf_*F$ by [def-weil-pbc-direct-image].
