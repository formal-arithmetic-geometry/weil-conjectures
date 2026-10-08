+++
id = "prop-pod-perfect-local-model"
kind = "theorem"
title = "The local finite projective model"
order = 2409
tags = ["latex:proposition"]
uses = ["def-pod-conventions", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-pbc-proetale-site", "thm-constructible-serre"]
+++
In the Poincare duality conventions of
this chapter, let $\Lambda=A_{E,n}$ be a finite ring and let $P$ be a
finite projective $\Lambda_X$-module on the
small pro-etale site of $X$.
Then $P$ is flat, so that $P$, regarded as a complex concentrated in
degree $0$, has finite $\operatorname{Tor}$-amplitude concentrated in
degree $0$ in the sense of
[def-weil-finite-tor-amplitude]; and $P$ is constructible with
finite stalks in the sense of
[def-weil-finite-torsion-constructibility]. Consequently a complex
that is quasi-isomorphic, locally on the small pro-etale site of $X$,
to a bounded complex of finite projective $\Lambda_X$-modules has
bounded constructible cohomology sheaves.

## Proof

A finite projective $\Lambda_X$-module $P$ is a direct summand of a
finite free module $\Lambda_X^r$, say $P=\ker(e)$ for an idempotent
endomorphism $e$ of $\Lambda_X^r$; in particular $P$ is flat, hence
$\operatorname{Tor}_i^{\Lambda_X}(P,-)=0$ for $i>0$, which is the
stated Tor-amplitude in the sense of
[def-weil-finite-tor-amplitude]. The constant sheaf
$\Lambda_X^r$ is a finite direct sum of copies of $\Lambda_X$, and
$\Lambda=\Lambda_{E,n}$ is a finite ring, so $\Lambda_X^r$ is locally
constant with finite stalks and therefore constructible in the sense of
[def-weil-finite-torsion-constructibility]. The constructible
$\Lambda$-sheaves form a weak Serre subcategory
([thm-constructible-serre]), so the kernel of the
idempotent $e$ is constructible as well, and its stalks, being
subgroups of the finite stalks of $\Lambda_X^r$, are finite; this
proves the first two assertions. For the last one, a bounded complex of
constructible sheaves has bounded cohomology, and each cohomology sheaf
is the kernel of a morphism of constructible sheaves modulo the image of
one, hence constructible by the same weak-Serre property.
