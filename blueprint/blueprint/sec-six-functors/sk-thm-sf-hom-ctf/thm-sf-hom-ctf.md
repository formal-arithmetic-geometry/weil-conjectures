+++
id = "thm-sf-hom-ctf"
kind = "theorem"
title = "Derived internal Hom at finite coefficients"
order = 2199
uses = ["cor-weil-finite-constructible-hom", "def-weil-site-perfect-complex", "lem-sf-ext-sheaf-constructible", "lem-sf-flat-model", "lem-sf-hom-finite-projective"]
+++
Let $A=A_{E,n}$, let $X$ be a finite-type $\overline{\mathbf F}_q$-scheme,
and let $K,M\in D^b_{ctf}(X_{\Et},A)$ have Tor amplitude in
$[a,b]$ and $[c,d]$, and suppose $\dim X\leq m$.
Then $R\mathcal Hom_A(K,M)$ belongs to $D^b_{ctf}(X_{\Et},A)$,
with Tor amplitude in $[c-b-2m,d-a+2m]$.
If $K$ is site-perfect, the sharper interval $[c-b,d-a]$ holds.

## Proof

The assertion is local on $X$; a finite affine cover reduces to
the separated case without increasing the dimension bound.
The general assertion and its dimension-dependent interval are
[cor-weil-finite-constructible-hom], proved from geometric
Verdier biduality and tensor preservation.
For the sharper assertion, locally on the site choose a finite projective model $P$ of $K$
in $[a,b]$, as in [def-weil-site-perfect-complex]. By
[lem-sf-hom-finite-projective], internal Hom is
$P^\vee\otimes_A^LM$. A bounded flat model of $M$, supplied by
[lem-sf-flat-model], makes this a bounded flat complex in
$[c-b,d-a]$. This proves the Tor bound; bounded constructibility is
[lem-sf-ext-sheaf-constructible]. Both assertions are local on the site.
