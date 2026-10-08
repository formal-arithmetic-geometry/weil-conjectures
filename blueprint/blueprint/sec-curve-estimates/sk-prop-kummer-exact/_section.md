+++
id = "sk-prop-kummer-exact"
kind = "section"
title = "Exactness of the Kummer sequence"
order = 875
uses = ["sk-def-curve", "sk-def-kummer"]
lean = ["AlgebraicGeometry.Scheme.kummerSequence_shortExact"]
+++
*Proposition (sketch).*

Let $C$ be a scheme and $n\ge1$ invertible on $C$ (e.g. $C$ as in
[sk-def-curve] over $k$ with $n$ prime to $\operatorname{char}k$).
Then the sequence of [sk-def-kummer] is an exact sequence of
sheaves on $C_{\Et}$.

## Proof

Exactness of a sequence of étale sheaves is checked on stalks at
geometric points, i.e. on the strictly henselian local rings
$\mathcal O_{C,\bar x}^{\mathrm{sh}}$. Left exactness holds by
definition of $\mu_n=\ker(n)$, so only surjectivity of
$\omega\mapsto\omega^n$ on stalks is at issue: given
$a\in(\mathcal O^{\mathrm{sh}}_{C,\bar x})^\times$, the monic
polynomial $T^n-a$ has derivative $nT^{n-1}$, and $n$ and $a$ are
units, so $T^n-a$ is separable; its reduction modulo the maximal
ideal therefore has a simple root in the separably closed residue
field, and Hensel's lemma for the strictly henselian ring
$\mathcal O^{\mathrm{sh}}_{C,\bar x}$ lifts that root to some
$\omega$ with $\omega^n=a$. Equivalently, and without passing to
stalks: $C[T]/(T^n-a)\to C$ is a finite étale surjection over the
locus where $a$ is a unit, so an $n$-th root of a unit exists
étale locally, which is exactly surjectivity of a map of étale
sheaves. Hence the sequence is exact.

Note the hypothesis cannot be dropped in general: if $n$ is
divisible by $\operatorname{char}k=p$ the map $\omega\mapsto\omega^n$
need *not* be an epimorphism of étale sheaves. (It is one for
$C=\Spec k$, $k$ being algebraically closed; but on $\mathbb G_{m,k}$
the unit $t$ acquires no $p$-th root in any separable extension of
$k(t)$, since $T^p-t$ is inseparable, so $t$ is not a $p$-th power
étale locally.) The two standard replacements differ: the fppf
Kummer sequence (Stacks `03PK`) keeps $\mu_p$ and
$\mathbb G_m$ but changes the topology, whereas the Artin–Schreier
sequence $0\to\Z/p\to\mathbb G_a\xrightarrow{F-1}\mathbb G_a\to0$
(Stacks `0A3J`) computes $\Z/p$-cohomology on the étale site
through $\mathbb G_a$.

Uses: [sk-def-curve], [sk-def-kummer]
