+++
id = "cor-sf-direct-image-ctf-proetale"
kind = "theorem"
title = "The pro-étale direct image for all finite-Tor objects"
order = 2195
tags = ["latex:corollary"]
uses = ["cor-sf-direct-image-ctf-etale-origin", "cor-sf-direct-image-ctf-nonproper", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-pbc-site-comparison-morphism", "def-weil-scheme-morphism-properties", "lem-sf-comparison-tor-amplitude", "lem-sf-etale-direct-image-vanishing", "lem-sf-proetale-constructible-origin", "prop-weil-pbc-comparison-direct-image", "thm-sf-direct-image-tor-amplitude"]
+++
Fix the global finite-field datum, a prime $\ell\ne p$, an integer
$n\geq1$, $A=A_{E,n}$, and the algebraically closed field
$k=\overline{\mathbf F}_q$. Let $X,Y$ be finite-type $k$-schemes with
$\dim X\leq d$, let $f:X\to Y$ be a
separated finite-type
morphism, and let $K\in D^b_{ctf}(X_{\Proet},A)$ be a bounded
constructible complex of $A$-modules on the small pro-étale site with
finite Tor amplitude in $[a,b]$, both notions being the intrinsic ones of
[def-weil-finite-torsion-constructibility] and
[def-weil-finite-tor-amplitude]. Then $Rf_*K$ is bounded
constructible on $Y_{\Proet}$ and has finite Tor amplitude in
$[a,b+2d]$. That is, clause (iii) of the finite-Tor preservation summary holds at
the finite coefficient stage $A$ for *every* object of
$D^b_{ctf}(X_{\Proet},A)$, with no restriction to the objects of étale
origin.

## Proof

By [lem-sf-proetale-constructible-origin] the object $K$ is of
étale origin: there are a bounded complex $K'$ with constructible
cohomology on $X_{\Et}$ and an isomorphism $K\cong\nu_X^*K'$, and by
[lem-sf-comparison-tor-amplitude](ii) the complex $K'$ has finite Tor
amplitude in $[a,b]$ on the étale site.
[cor-sf-direct-image-ctf-nonproper], whose two inputs are
[thm-sf-direct-image-tor-amplitude] and
[lem-sf-etale-direct-image-vanishing], therefore gives a bounded
constructible étale complex $Rf_{\Et,*}K'$ with finite Tor amplitude in
$[a,b+2d]$. The morphism $f$ is of finite type, hence quasi-compact and
quasi-separated, so the comparison direct image of
[prop-weil-pbc-comparison-direct-image] gives an isomorphism

$$
Rf_{\Proet,*}\nu_X^*K'\cong\nu_Y^*Rf_{\Et,*}K',
$$

and [lem-sf-comparison-tor-amplitude](i) gives finite Tor amplitude in
$[a,b+2d]$ and bounded constructibility for the right-hand side. As in
[cor-sf-direct-image-ctf-etale-origin] this is clause (iii) of
the finite-Tor preservation summary at the finite coefficient stage $A$ for the
object $K$.
