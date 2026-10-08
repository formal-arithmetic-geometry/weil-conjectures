+++
id = "lem-weil-bounded-finite-tor-perfect"
kind = "lemma"
title = "Bounded complexes of finite Tor amplitude are perfect"
order = 2068
uses = ["def-weil-derived-tensor", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-site-perfect-complex"]
+++
Let $R$ be a Noetherian ring and let $K$ be a bounded complex of finite
$R$-modules with finite Tor amplitude in the sense of
[def-weil-finite-tor-amplitude]: there are integers $a\le b$ with
$\mathcal H^i(K\otimes^L_RM)=0$ for every $i\notin[a,b]$ and every
$R$-module $M$. Then $K$ is quasi-isomorphic to a bounded complex of
finite projective $R$-modules concentrated in degrees $[a,b]$. If
$R$ is local, projective is free, so $K$ is then site-perfect in the
sense of [def-weil-site-perfect-complex].

## Proof

This is the criterion of the Stacks Project, More on Algebra,
Lemma 15.76.2, [Tag 0658](https://stacks.math.columbia.edu/tag/0658),
with the definition of a perfect complex, Definition 15.76.1,
[Tag 0657](https://stacks.math.columbia.edu/tag/0657): an object of
$D(R)$ is perfect, that is quasi-isomorphic to a bounded complex of
finite projective $R$-modules, if and only if it is pseudo-coherent and of
finite Tor dimension, and a perfect complex of Tor amplitude in $[a,b]$
is quasi-isomorphic to a complex of finite projective modules vanishing
outside $[a,b]$.

Both hypotheses are available here. *Finite Tor dimension* is the
hypothesis of the statement. *Pseudo-coherence:* each term $K^i$ of
the bounded complex is a finite module over the Noetherian ring $R$, hence
finitely presented; resolving the terms by finite free modules and taking
the total complex of the resulting double complex, with the usual signs,
gives a bounded-above complex of finite free $R$-modules together with a
quasi-isomorphism onto $K$, which is precisely the condition that $K$ is
pseudo-coherent. Finally, over a local ring a finite projective module is
free: a finitely generated projective module is a direct summand of a finite
free module, and over a local ring such a summand has constant rank, hence
is free. A finite module over the Noetherian ring $R$ is perfect if and
only if it admits a finite resolution by finite projective modules, which is
the case at hand; this is Stacks Project, More on Algebra, Lemma 15.76.3,
[Tag 066Q](https://stacks.math.columbia.edu/tag/066Q).
