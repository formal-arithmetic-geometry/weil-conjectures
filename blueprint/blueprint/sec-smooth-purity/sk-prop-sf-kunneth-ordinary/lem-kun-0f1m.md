+++
id = "lem-kun-0f1m"
kind = "lemma"
title = "Tor amplitude and K-flat resolutions"
order = 1725
uses = ["def-kun-derived-tensor", "def-kun-tor-amplitude", "def-kun-truncations", "lem-kun-flat-resolution-existence", "lem-kun-kflat-criteria", "lem-kun-tor-cokernel-flat"]
+++
Let $\Lambda$ be a commutative ring, $T$ a scheme,
$E\in D(T_{\Et},\Lambda)$, and $a\in\mathbf Z$. Then $E$ has tor
amplitude in $[a,\infty)$ in the sense of
[def-kun-tor-amplitude] if and only if $E$ can be represented
by a K-flat complex $\mathcal E^\bullet$ of flat
$\Lambda_T$-module sheaves with $\mathcal E^i=0$ for $i<a$;
moreover $\mathcal E^\bullet$ may be chosen so that any pullback is
again K-flat with flat terms. (*Source:* the argument is the one
of Stacks Project, [Tag
`0F1M`](https://stacks.math.columbia.edu/tag/0F1M); the only input used is the existence of flat resolutions
of [lem-kun-flat-resolution-existence].)

## Proof

*The model gives the amplitude.* Suppose $E$ is represented by a
K-flat complex $\mathcal E^\bullet$ of flat sheaves with
$\mathcal E^i=0$ for $i<a$, and let $\mathcal M$ be a
$\Lambda_T$-module sheaf placed in degree $0$. Since
$\mathcal E^\bullet$ is K-flat, the derived tensor product
$E\kunotimes{\Lambda}\mathcal M$ of
[def-kun-derived-tensor] is computed by
$\mathcal E^\bullet\otimes_\Lambda\mathcal M$, whose terms in degrees
$<a$ vanish; hence $H^i(E\kunotimes{\Lambda}\mathcal M)=0$ for
$i<a$, so $E$ has tor amplitude in $[a,\infty)$ in the sense of
[def-kun-tor-amplitude].
*The amplitude gives the model.* Assume $E$ has tor amplitude in
$[a,\infty)$. Taking $\mathcal M=\Lambda_T$ shows $H^i(E)=0$ for
$i<a$. By [lem-kun-flat-resolution-existence] there is a K-flat
complex $\mathcal K^\bullet$ with flat terms and a quasi-isomorphism
$\mathcal K^\bullet\to E$. For every $\mathcal M$ the cohomology of
$\mathcal K^\bullet\otimes_\Lambda\mathcal M$ computes
$H^*(E\kunotimes{\Lambda}\mathcal M)$, so the tor-amplitude
hypothesis gives
$H^n(\mathcal K^\bullet\otimes_\Lambda\mathcal M)=0$ for all $n<a$
and all $\mathcal M$; by [lem-kun-tor-cokernel-flat] the sheaf

$$
\mathcal N=\operatorname{coker}\bigl(\mathcal K^{a-1}\to\mathcal
K^a\bigr)
$$

is flat. Set

$$
\mathcal E^\bullet=\tau_{\ge a}\mathcal K^\bullet=
\bigl(\cdots\to0\to\mathcal N\to\mathcal K^{a+1}\to
\mathcal K^{a+2}\to\cdots\bigr),
$$

the good truncation of $\mathcal K^\bullet$ in the sense of
[def-kun-truncations], with the degree-$a$ term replaced by the flat
sheaf $\mathcal N$. Since $H^i(\mathcal K^\bullet)=H^i(E)=0$ for
$i<a$, the natural map $\mathcal E^\bullet\to\mathcal K^\bullet$ is
a quasi-isomorphism, and $\mathcal E^i=0$ for $i<a$. Its kernel

$$
\mathcal L^\bullet=\bigl(\cdots\to\mathcal K^{a-1}\to\mathcal
I\to0\to\cdots\bigr),\qquad
\mathcal I=\operatorname{im}\bigl(\mathcal K^{a-1}\to\mathcal
K^a\bigr),
$$

is a bounded-above complex of flat sheaves: $\mathcal I$ is flat,
being the kernel of the surjection $\mathcal K^a\twoheadrightarrow \mathcal N$ between the flat sheaves $\mathcal K^a$ and
$\mathcal N$ (the Tor sequence
$0=\operatorname{Tor}_1(\mathcal K^a,\mathcal M)\to \operatorname{Tor}_1(\mathcal N,\mathcal M)=0\to\mathcal I\otimes_\Lambda\mathcal M\to\mathcal K^a\otimes_\Lambda\mathcal M\to\mathcal N\otimes_\Lambda\mathcal M\to0$ is exact). Hence
$\mathcal L^\bullet$ is K-flat by [lem-kun-kflat-criteria](1),
and the short exact sequence
$0\to\mathcal L^\bullet\to\mathcal K^\bullet\to\mathcal E^\bullet\to0$ exhibits $\mathcal E^\bullet$ as the cone of a map of
K-flat complexes, so $\mathcal E^\bullet$ is K-flat by
[lem-kun-kflat-criteria](2).
*Pullback.* Pullback along a morphism of schemes is exact, carries
flat module sheaves to flat module sheaves, and commutes with tensor
products and with the truncation construction above; applied to a
K-flat complex with flat terms it again produces a K-flat complex with
flat terms (the pullback of an acyclic complex is acyclic), and applied
to the quasi-isomorphisms above it produces the corresponding
quasi-isomorphisms. Hence the model $\mathcal E^\bullet$ may be chosen
so that every pullback is again K-flat with flat terms, as asserted.
