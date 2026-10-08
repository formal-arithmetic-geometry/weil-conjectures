+++
id = "thm-sf-direct-image-tor-amplitude"
kind = "theorem"
title = "Direct image and finite Tor amplitude"
order = 2066
uses = ["def-sf-uniform-direct-image-vanishing", "def-weil-derived-tensor", "def-weil-finite-tor-amplitude", "def-weil-pbc-direct-image", "def-weil-pbc-etale-site", "lem-exc-residue-tor-test", "lem-sf-flat-model", "lem-sf-projection-finite-constant", "sbc-def-coefficient-conventions", "thm-dg-finite-type-constructibility", "thm-sp-truncation-e2"]
+++
Fix an algebraically closed field $k$, a prime
$\ell\ne\operatorname{char}k$, $n\geq1$,
$A=A_{E,n}$, finite-type
$k$-schemes $X,Y$ and a separated finite-type morphism $f:X\to Y$.
Assume $\operatorname{UDV}(f,A;N)$ for an integer $N\geq0$, in the sense
of [def-sf-uniform-direct-image-vanishing]. Let $K$ be a bounded
constructible complex of $A$-modules on the small étale site $X_{\Et}$
with finite Tor amplitude in
$[a,b]$, the finite-Tor condition being the one of the étale clause of
[lem-sf-flat-model]. Then $Rf_*K$ is bounded constructible on
$Y_{\Et}$ and has finite Tor amplitude in $[a,b+N]$.

## Proof

Let $P$ be the bounded flat model of $K$ given by the étale clause of
[lem-sf-flat-model]: $P\cong K$ is a bounded complex of flat
$A_X$-module sheaves with $P^q=0$ for $q\notin[a,b]$. Its terms
vanish outside $[a,b]$, so $\mathcal H^q(K)=0$ for $q\notin[a,b]$.
Put $\kappa=A/(\varpi_E)$, the residue field of the local ring $A$. The
constant sheaf $\kappa_X$ is a sheaf of $A$-modules placed in degree
zero, so the definition of finite Tor amplitude gives

$$
\mathcal H^q\bigl(K\otimes^L_A\kappa_X\bigr)=0\qquad(q\notin[a,b]).
$$

Apply the truncation spectral sequence of [thm-sp-truncation-e2] to
the left exact direct image functor and to the complex
$K\otimes^L_A\kappa_X$:

$$
E_2^{p,q}=R^pf_*\bigl(\mathcal H^q(K\otimes^L_A\kappa_X)\bigr)
\ \Longrightarrow\ \mathcal H^{p+q}\bigl(Rf_*(K\otimes^L_A\kappa_X)\bigr).
$$

Only $q\in[a,b]$ occurs, and only $p\leq N$ occurs by
$\operatorname{UDV}(f,A;N)$; hence
$\mathcal H^n(Rf_*(K\otimes^L_A\kappa_X))=0$ for $n\notin[a,b+N]$.

The coefficient ring $A$ is finite and annihilated by the integer
$\ell^n$, which is invertible in $k$ by the stated characteristic
assumption; so
[thm-dg-finite-type-constructibility] makes $Rf_*K$ a bounded
constructible complex on $Y_{\Et}$, with constructible cohomology
sheaves.

The module $\kappa$ is finitely presented over the Noetherian ring $A$,
so the projection formula of [lem-sf-projection-finite-constant]
identifies

$$
(Rf_*K)\otimes^L_A\kappa_Y\cong Rf_*\bigl(K\otimes^L_A\kappa_X\bigr),
$$

and by the spectral-sequence computation this complex has cohomology only
in $[a,b+N]$. The residue test [lem-exc-residue-tor-test] applies to
the bounded complex $Rf_*K$, whose cohomology sheaves are constructible,
and to the residue field $\kappa=A/(\varpi_E)$; it converts the
concentration just proved into finite Tor amplitude of $Rf_*K$ in
$[a,b+N]$, which is the assertion.
