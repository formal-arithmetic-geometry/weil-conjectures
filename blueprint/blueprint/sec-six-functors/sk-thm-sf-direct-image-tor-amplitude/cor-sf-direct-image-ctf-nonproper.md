+++
id = "cor-sf-direct-image-ctf-nonproper"
kind = "theorem"
title = "The direct image on finite Tor amplitude for a non-proper morphism"
order = 2191
tags = ["latex:corollary"]
uses = ["def-sf-uniform-direct-image-vanishing", "def-weil-finite-tor-amplitude", "def-weil-pbc-etale-site", "def-weil-scheme-morphism-properties", "lem-sf-etale-direct-image-vanishing", "thm-sf-direct-image-tor-amplitude"]
+++
Fix the global finite-field datum, a prime $\ell\ne p$, $n\geq1$,
$A=A_{E,n}$, and the algebraically closed field
$k=\overline{\mathbf F}_q$. Let $X,Y$ be finite-type $k$-schemes with
$\dim X\leq d$, let $f:X\to Y$ be a
separated finite-type
morphism, and let $K$ be a bounded constructible complex of
$A$-modules on the small étale site $X_{\Et}$ with finite
Tor amplitude in $[a,b]$. Then
$Rf_*K$ is bounded constructible on $Y_{\Et}$ and has finite Tor
amplitude in $[a,b+2d]$. No properness and no compactifiability of $f$
is assumed.

## Proof

By [lem-sf-etale-direct-image-vanishing] the hypothesis
$\operatorname{UDV}(f,A;2d)$ of
[def-sf-uniform-direct-image-vanishing] holds for $f$ on the
small étale sites, for every sheaf of
$A$-modules; [thm-sf-direct-image-tor-amplitude] with $N=2d$ then
gives the assertion.
