+++
id = "lem-sf-tensor-ctf"
kind = "lemma"
title = "The derived tensor product on the finite-Tor subcategories"
order = 2119
uses = ["def-weil-derived-cohomology-sheaves", "def-weil-derived-tensor", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "lem-sf-flat-model", "lem-sf-tor-sheaf-constructible", "thm-constructible-serre"]
+++
Fix the global finite-field datum, a prime $\ell\ne p$, $n\geq1$, put
$A=A_{E,n}$, and let $X$ be a
finite-type
$k$-scheme. Let $K\in D^b_{ctf}(X,A)$ have
finite Tor amplitude in $[a,b]$,
and let $M\in D^b_c(X,A)$ be
bounded constructible.
Then:

1. **(i)** $K\otimes_A^LM$ belongs to $D^b_c(X,A)$;
1. **(ii)** if in addition $M\in D^b_{ctf}(X,A)$ has finite Tor amplitude
in $[c,d]$, then $K\otimes_A^LM$ belongs to $D^b_{ctf}(X,A)$, with
finite Tor amplitude in $[a+c,b+d]$.

## Proof

By [lem-sf-flat-model] fix an isomorphism $K\cong P$ with $P$ a
bounded complex of flat $A_X$-module sheaves, $P^q=0$ for
$q\notin[a,b]$. Such a $P$ is K-flat, so by
[def-weil-derived-tensor] the object $K\otimes_A^LM$ is computed by
the ordinary tensor complex $P\otimes_AM$.

*(ii).* Apply [lem-sf-flat-model] again to obtain a bounded flat
model $Q$ of $M$ with $Q^r=0$ for $r\notin[c,d]$. Then
$K\otimes_A^LM\cong P\otimes_AQ$, the total complex of the double complex
with terms $P^q\otimes_AQ^r$; each of these terms is flat, the tensor
product of a flat sheaf with a flat sheaf being flat, and they occur only in
total degree $q+r\in[a+c,b+d]$. So $P\otimes_AQ$ is a bounded complex of
flat sheaves concentrated in $[a+c,b+d]$, and [lem-sf-flat-model]
gives finite Tor amplitude in $[a+c,b+d]$ for $K\otimes_A^LM$;
bounded constructibility is (i).

*(i), boundedness.* Since $M$ is bounded constructible, its
cohomology sheaves vanish outside an interval $[c',d']$, and the
truncation $\sigma_{\geq c'}\sigma_{\leq d'}M$ is a bounded complex $C$ of
$A_X$-module sheaves with $M\cong C$ and $C^i=0$ for
$i\notin[c',d']$. Then $K\otimes_A^LM\cong P\otimes_AC$, a complex whose
terms occur only in the finite range $[a+c',b+d']$; hence
$K\otimes_A^LM$ is bounded.

*(i), constructibility.* The functor $-\otimes_A^L-$ is exact on
triangulated categories, and a bounded constructible complex is built from
the shifts $\mathcal H^p(K)[-p]$, respectively $\mathcal H^q(M)[-q]$, of
its constructible cohomology sheaves by finitely many extensions, the
successive quotients of the filtration by the truncations $\tau_{\geq p}$.
It therefore suffices to show that
$\mathcal H^r(F\otimes_A^LG)$ is constructible for constructible sheaves
$F$ and $G$ in single degrees: this is
[lem-sf-tor-sheaf-constructible]. The propagation through the
extensions is the long exact cohomology sequence of a distinguished
triangle, in which each cohomology sheaf of the middle term is an extension
of a subobject of a cohomology sheaf of one outer term by a quotient of a
cohomology sheaf of the other; constructible sheaves are closed under
kernels, cokernels and extensions, which is the weak Serre property of
[thm-constructible-serre] of the proper-base-change chapter,
in the definition-level form of
[def-weil-finite-torsion-constructibility] on the pro-étale site
(local constancy is a condition local for the topology, and the constant
sheaves form an abelian category). Hence $\mathcal H^r(K\otimes_A^LM)$ is
constructible for every $r$, which with the boundedness just proved is
(i).
