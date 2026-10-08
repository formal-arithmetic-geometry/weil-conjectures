+++
id = "lem-sf-comparison-tor-amplitude"
kind = "lemma"
title = "Finite Tor amplitude under the site comparison"
order = 2067
uses = ["def-weil-derived-pullback-tensor-hom", "def-weil-derived-tensor", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-pbc-constructible-complexes", "def-weil-pbc-site-comparison-morphism", "lem-exc-constant-inverse-image-flat", "lem-sf-flat-model", "lem-sf-proetale-constructible-origin", "lem-sf-pullback-tor-amplitude", "prop-weil-pbc-proetale-constant-ring-map", "thm-weil-pbc-site-comparison"]
+++
Fix the global finite-field datum, a prime $\ell\ne p$, an integer
$n\geq1$ and $A=A_{E,n}$, and let $T$ be a scheme on which $\ell$ is
invertible. Write $\nu_T:T_{\Proet}\to T_{\Et}$ for the comparison
morphism of sites.

1. **(i)** If $K'\in D^b_c(T_{\Et},A)$ has finite Tor amplitude in
$[a,b]$ on the étale site, in the sense of the étale clause of
[lem-sf-flat-model], then $\nu_T^*K'$ is bounded constructible on
$T_{\Proet}$ and has finite Tor amplitude in $[a,b]$ in the sense of
[def-weil-finite-tor-amplitude].
1. **(ii)** Conversely, if $K\in D^b_c(T_{\Proet},A)$ has finite Tor
amplitude in $[a,b]$ and $K\cong\nu_T^*K'$ for a bounded-below complex
$K'$ of $A$-module sheaves on $T_{\Et}$, then $K'$ has finite Tor
amplitude in $[a,b]$ on the étale site.

## Proof

*(i).* By the étale clause of [lem-sf-flat-model] the complex
$K'$ is isomorphic to a bounded complex $P'$ of flat
$A_{T,\Et}$-module sheaves with $P'^q=0$ for $q\notin[a,b]$. The
pullback $\nu_T^*P'$ is a bounded complex of flat
$A_{T,\Proet}$-module sheaves with the same interval: flatness is the
condition of [lem-exc-constant-inverse-image-flat], and the inverse
image of a flat module sheaf is flat, as recalled in the proof of
[lem-sf-pullback-tor-amplitude]. A bounded complex of flat sheaves is
K-flat, by the argument of [lem-sf-flat-model]: for an acyclic complex
$Q$ each term $\nu_T^*P'^q\otimes_AQ$ is acyclic and the total complex
of the resulting double complex is acyclic. Hence for every sheaf $N$ of
$A$-modules on $T_{\Proet}$ placed in degree zero the object
$\nu_T^*K'\otimes_A^LN$ is computed by the ordinary tensor complex
$\nu_T^*P'\otimes_AN$, whose terms $\nu_T^*P'^q\otimes_AN$ sit in degree
$q$, by flatness of $\nu_T^*P'^q$; its cohomology therefore vanishes
outside $[a,b]$, which is (i). Bounded constructibility of $\nu_T^*K'$
is [lem-sf-proetale-constructible-origin].
*(ii).* Let $N$ be a sheaf of $A$-modules on $T_{\Et}$ placed in
degree zero. By the compatibility of the inverse image with the derived
tensor product, [def-weil-derived-pullback-tensor-hom], and because
the pullback of the constant coefficient sheaf is the constant coefficient
sheaf, [prop-weil-pbc-proetale-constant-ring-map],

$$
\nu_T^*\bigl(K'\otimes_A^LN\bigr)
\cong\nu_T^*K'\otimes_A^L\nu_T^*N
\cong K\otimes_A^L\nu_T^*N,
$$

and the right-hand side has cohomology only in $[a,b]$ by the assumed
finite Tor amplitude of $K$, the sheaf $\nu_T^*N$ being a sheaf of
$A$-modules on $T_{\Proet}$ placed in degree zero. The comparison
pullback reflects the vanishing of cohomology: by
[thm-weil-pbc-site-comparison] the unit is an isomorphism
$\operatorname{id}\cong R\nu_{T,*}\nu_T^*$ on bounded-below complexes, so
$\nu_T^*C\cong0$ forces $C\cong R\nu_{T,*}\nu_T^*C\cong0$. Hence
$K'\otimes_A^LN$ has cohomology only in $[a,b]$, for every such $N$,
which is the finite Tor amplitude of $K'$ in $[a,b]$ in the sense of
[def-weil-finite-tor-amplitude] read on the étale site.
