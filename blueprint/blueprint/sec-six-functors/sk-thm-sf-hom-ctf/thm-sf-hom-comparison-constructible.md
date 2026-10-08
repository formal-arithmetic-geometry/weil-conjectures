+++
id = "thm-sf-hom-comparison-constructible"
kind = "theorem"
title = "Internal-Hom comparison for finite-Tor constructible inputs"
order = 2198
uses = ["def-weil-pbc-site-comparison-morphism", "lem-weil-finite-duality-site-comparison"]
+++
Let $X$ be a finite-type $\overline{\mathbf F}_q$-scheme,
let $\nu_X:X_{\Proet}\to X_{\Et}$ be the site comparison,
let $K\in D^b_{ctf}(X_{\Et},A_{E,n})$, and let
$M\in D^b_c(X_{\Et},A_{E,n})$. Then

$$
\nu_X^*R\mathcal Hom_A(K,M)\longrightarrow
R\mathcal Hom_A(\nu_X^*K,\nu_X^*M)
$$

is an isomorphism.

## Proof

The assertion is local on $X$, since internal Hom and site
comparison restrict to open subschemes. A finite affine cover
therefore reduces to separated $X$. This is then the internal-Hom assertion of
[lem-weil-finite-duality-site-comparison]. Its proof uses
extension by zero from site-perfect strata and the closed-support
triangle to compare exceptional restriction, so it applies to a
general finite-Tor constructible first argument.
