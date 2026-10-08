+++
id = "lem-exc-dvr-galois"
kind = "lemma"
title = "The prime-to-characteristic local Galois calculation"
order = 1916
uses = ["def-exc-continuous-cohomology", "def-weil-pbc-henselian-terminology", "lem-exc-procyclic-two-term"]
+++
Let $R$ be an excellent discrete valuation ring which is
strictly henselian,
with algebraically closed residue field of characteristic $p>0$.
Put $F=\operatorname{Frac}(R)$, let $G=\operatorname{Gal}(F^{\rm sep}/F)$,
and fix $\ell\neq p$. If $A$ is a finite ring killed by a power
of $\ell$, then for every
discrete continuous
$A[G]$-module $M$ one has

$$
H^q(G,M)=0\quad(q>1).
$$

If $M$ is finite, then $H^0(G,M)$ and $H^1(G,M)$ are finite.

## Proof

We give the ramification and homological calculations separately.
For a finite Galois extension of $F$, the integral closure of $R$
is finite by excellence and is local by henselianity. Its residue field
is the given algebraically closed field. If $t$ is a uniformizer
of that integral closure, the map
$\sigma\mapsto\sigma(t)/t\bmod t$ is the tame inertia character.
Its image is a finite cyclic group of order prime to $p$.
Its kernel is a $p$-group: filter the kernel by the order of
$\sigma(t)-t$; the successive nontrivial quotients embed in the
additive residue field and hence have exponent $p$, and the
filtration terminates for a finite group. The equality between degree
and ramification index used here follows from the length of the finite
free integral closure modulo a uniformizer. This is the elementary
discrete-valuation ramification calculation; for its algebraic formulation
see [Stacks Project,
Section 15.114](https://stacks.math.columbia.edu/tag/09E3).

Taking inverse limits of finite Galois extensions therefore gives

$$
1\longrightarrow P\longrightarrow G\longrightarrow
\prod_{r\neq p}\mathbf Z_r(1)\longrightarrow1,
$$

where $P$ is pro-$p$. The tame quotient is the whole displayed
product: for every $m$ prime to $p$, the roots of unity lift to
$R$ by the henselian property of
[def-weil-pbc-henselian-terminology], and adjoining an $m$-th
root of a uniformizer gives a cyclic extension of degree $m$.
Let $H$ be the inverse image of
$\prod_{r\neq p,\ell}\mathbf Z_r(1)$. Every finite quotient of
$H$ has order prime to $\ell$, and $G/H=\mathbf Z_\ell(1)$.

The functor $M\mapsto M^H$ is exact. Indeed, to lift an invariant
element through a surjection, first choose any lift. Its finite orbit
generates a finite module, since $A$ is finite. Its action factors
through a finite quotient $Q$ of $H$. Averaging the lift by
$|Q|^{-1}\sum_{h\in Q}h$ gives an invariant lift. Thus its
higher derived functors vanish. It also sends injectives to injectives
as a functor to $G/H$-modules, since its left adjoint is exact
inflation. Applying it to an injective resolution, and then taking
$G/H$-invariants, gives

$$
R\Gamma(G,M)=R\Gamma(\mathbf Z_\ell(1),M^H)
$$

for the continuous cohomology of [def-exc-continuous-cohomology].

Choose a topological generator $\tau$ of $\mathbf Z_\ell(1)$.
Its continuous invariants are computed by

$$
[\,M^H\xrightarrow{\tau-1}M^H\,]
\quad\text{in degrees }0,1.
$$

This formula is [lem-exc-procyclic-two-term], applied after
identifying the chosen generator with $1\in\mathbf Z_\ell$.
It proves vanishing above degree one. If $M$ is finite, both
terms are finite; their kernel and cokernel are finite as well.
