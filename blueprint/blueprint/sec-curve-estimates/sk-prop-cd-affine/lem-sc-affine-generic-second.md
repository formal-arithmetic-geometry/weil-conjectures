+++
id = "lem-sc-affine-generic-second"
kind = "lemma"
title = "Second cohomology of a generic extension on an affine curve"
order = 1017
uses = ["def-sc-curves", "def-sc-function-field", "def-weil-pbc-etale-cohomology", "def-weil-pbc-etale-sheaves", "lem-exc-field-discrete-modules", "lem-sc-affine-constant-second", "lem-sc-finite-extension-affine-model", "lem-sc-sylow-module-filtration", "lem-sc-zero-generic-acyclic", "lem-weil-pbc-cohomology-filtered-colimit", "lemma-weil-pbc-finite-direct-image-exact"]
+++
Let $C/k$ be a smooth integral affine
connected curve over algebraically closed $k$
and $\eta:\operatorname{Spec}k(C)\to C$ its
generic point.
For every torsion etale sheaf
$M$ on $\operatorname{Spec}k(C)$, one has
$H^2(C,\eta_*M)=0$, with
etale cohomology.

## Proof

First let $M$ be finite $\ell$-primary. Use
[lem-exc-field-discrete-modules], [lem-sc-sylow-module-filtration]
to choose a finite separable extension $K'/K$, $K=k(C)$,
of degree $d$ prime to $\ell$, such that $M'=M|_{K'}$
has a filtration by trivial $\mathbf F_\ell$-modules.
Write $a:\eta'=\operatorname{Spec}K'\to\eta$.
The finite etale trace on the field is the sum over the $d$
geometric points of its fibre. The unit and this sum give

$$
M\longrightarrow a_*a^*M\longrightarrow M
$$

with composite $d\,\mathrm{id}$. Multiplication by $d$ is
invertible, so this is a splitting after rescaling the sum.
No trace for a ramified morphism is being asserted.

Use [lem-sc-finite-extension-affine-model] to obtain
$h:C'\to C$ and the generic point map $b:\eta'\to C'$.
The equality $h b=\eta a$ gives
$\eta_*a_*M'=h_*b_*M'$. Applying $\eta_*$ to the splitting
makes $\eta_*M$ a direct summand of this sheaf.
Finite direct image is exact by
[lemma-weil-pbc-finite-direct-image-exact], so it remains to
prove $H^2(C',b_*M')=0$.

For a filtration step $0\to M_1\to M_2\to M_3\to0$, put
$G_i=b_*M_i$ and $I=\operatorname{im}(G_2\to G_3)$.
Although $b_*$ need not be exact, its left exactness gives
$0\to G_1\to G_2\to I\to0$, and $G_3/I$ has zero generic
restriction. By [lem-sc-zero-generic-acyclic],
$H^2(C',I)\simeq H^2(C',G_3)$.
The other long exact sequence shows that vanishing for $G_1$
and $G_3$ implies vanishing for $G_2$.
For a trivial quotient, $b_*\mathbf F_\ell=\mathbf F_\ell$:
each connected normal etale curve is integral, so a locally
constant function on its generic point extends uniquely.
The base case is [lem-sc-affine-constant-second].
Induction through the filtration proves the finite case.

A general torsion $G_K$-module is the directed union of finite
stable submodules: each orbit is finite by continuity, and a
finite set of torsion generators generates a finite group.
Separate the finitely many primary parts of each finite module.
The functor $\eta_*$ commutes with this union. Indeed, on a
quasi-compact etale test curve the generic fibre is a finite
disjoint union of spectra of finite separable extensions;
sections are a finite product of invariant groups. Invariants
commute with directed unions of submodules, directly from their
definition. Finally
[lem-weil-pbc-cohomology-filtered-colimit] proves the
assertion for the union.
