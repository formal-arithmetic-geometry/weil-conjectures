+++
id = "thm-weil-pbc-weak-etale-strict-local"
kind = "theorem"
title = "A weakly etale local map over a strict henselian ring"
order = 1219
uses = ["def-weil-pbc-henselian-terminology", "def-weil-pbc-ind-etale-algebra", "lem-weil-pbc-ind-etale-stability", "lem-weil-pbc-weak-etale-field", "lem-weil-pbc-weak-etale-integral-closure"]
+++
Let $A\to B$ be a local map of local rings. If $A$ is strictly henselian
[def-weil-pbc-henselian-terminology] and the map is weakly etale
[def-weil-pbc-ind-etale-algebra], it is an isomorphism.

## Proof

The local flat map $A\to B$ is faithfully flat. For each prime $\mathfrak
p\subset A$, its fibre is ind-etale over $\kappa(\mathfrak p)$, by
[lem-weil-pbc-ind-etale-stability] and [lem-weil-pbc-weak-etale-field]. If
that fibre has two primes, its finite etale subalgebras separate them by an
idempotent. If instead it has a residue extension larger than
$\kappa(\mathfrak p)$, a finite separable subextension splits into at least
two factors after a finite separable field extension. In either case there is
an algebraic field extension $L/\kappa(\mathfrak p)$ such that $B\otimes_AL$
has a nontrivial idempotent.

Let $A'$ be the integral closure of $A/\mathfrak p$ in $L$. Its fraction
field is $L$, by clearing denominators in a monic algebraic equation. It is a
henselian local ring: each finite domain subalgebra over the henselian local
ring $A/\mathfrak p$ is local, since the idempotents of its finite residue
algebra lift and a domain cannot split. These local finite algebras form a
filtered union; the finite equations for henselian lifting descend to a
member of that union. Its residue extension over the separably closed residue
field of $A$ is purely inseparable. This also shows that $A'$ is strictly
henselian in [def-weil-pbc-henselian-terminology].

The integral extension $B\to B\otimes_AA'$ has exactly one maximal ideal.
Indeed, maximal ideals lie above the maximal ideal of $B$; its fibre, after
removing nilpotents, is the tensor product of its residue field with a purely
inseparable field extension, which has one prime. Thus $B\otimes_AA'$ is
local. By [lem-weil-pbc-weak-etale-integral-closure] it is integrally closed
in $B\otimes_AL$. Every idempotent of the latter ring is integral and hence
belongs to this local ring, where it must be zero or one. This contradicts
the preceding paragraph. Therefore every fibre of $\operatorname{Spec}B\to
\operatorname{Spec}A$ is a single point with unchanged residue field.

The diagonal is now surjective on points after every field extension. Its
defining ideal $J$ in $B\otimes_AB$ is therefore nil, and its quotient is
flat by weak etaleness. The flat-quotient criterion says that for each $z\in
J$ there is $e\in J$ with $z=ze$; it follows by tensoring the inclusion
$(z)\subset B\otimes_AB$ with the quotient. Since $e$ is nilpotent, $1-e$ is
invertible, so $z=0$. Thus $B\otimes_AB\to B$ is an isomorphism. Faithfully
flat descent, in its equalizer form for modules, finally gives $A=B$. This is
the local calculation of Olivier; see
[Stacks Project, Tag 092Z](https://stacks.math.columbia.edu/tag/092Z) for its
customary formulation.
