+++
id = "lem-kun-leray-unbdd"
kind = "lemma"
title = "Unbounded Leray for finite cohomological dimension"
order = 1697
uses = ["def-kun-cd", "def-kun-rgamma-unbounded", "def-weil-pbc-derived-categories", "def-weil-pbc-direct-image", "def-weil-pbc-hypercohomology-filtrations", "def-weil-pbc-scheme-conventions", "lem-kun-leray-bdd"]
+++
Let $f:X\to Y$ be a qcqs morphism of schemes with
$\kuncd(f)<\infty$ and let $n\ge1$. Then

$$
\RGamma(X_{\Et},E)\cong\RGamma\bigl(Y_{\Et},Rf_*E\bigr)
$$

canonically for every $E\in D(X_{\Et},\kunZn)$.

## Proof

For $E\in D(X_{\Et},\kunZn)$ the Grothendieck spectral sequence of
the composite $\Gamma(Y_{\Et},-)\circ Rf_*$
([def-weil-pbc-hypercohomology-filtrations] in the
global-section form) has

$$
E_2^{p,q}=H^p\bigl(Y_{\Et},R^qf_*E\bigr)
\Longrightarrow H^{p+q}(X_{\Et},E),
$$

the abutment being $\RGamma(X_{\Et},E)$ by
[def-kun-rgamma-unbounded]. Since $\kuncd(f)<\infty$ by
hypothesis, $R^qf_*E=0$ for all $q>d$ with $d=\kuncd(f)$
([def-kun-cd]), so the spectral sequence is confined to the
finitely many columns $0\le q\le d$; a half-plane spectral sequence
with finitely many columns converges strongly without any boundedness
hypothesis on $E$, and its edge map in degree $n$ is the canonical
map $H^n(Y_{\Et},Rf_*E)\to H^n(X_{\Et},E)$. For $E$ bounded below
this edge map is an isomorphism by [lem-kun-leray-bdd]; the
finiteness of the columns forces the same for arbitrary $E$, since
each abutment is computed from finitely many columns. Hence
$\RGamma(X_{\Et},E)\cong\RGamma(Y_{\Et},Rf_*E)$.
