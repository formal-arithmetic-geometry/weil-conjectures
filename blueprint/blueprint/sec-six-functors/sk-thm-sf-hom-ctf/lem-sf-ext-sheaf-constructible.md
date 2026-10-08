+++
id = "lem-sf-ext-sheaf-constructible"
kind = "lemma"
title = "Constructible internal Hom with a site-perfect first variable"
order = 2197
uses = ["def-weil-site-perfect-complex", "lem-sf-hom-finite-projective", "thm-constructible-serre"]
+++
If $K$ is site-perfect and $M$ is bounded constructible on
$X_{\Et}$, then every cohomology sheaf of
$R\mathcal Hom_A(K,M)$ is constructible. In particular, for a finite
locally free sheaf $F$ and a constructible sheaf $G$,
$\mathcal Ext_A^r(F,G)=0$ for $r\ne0$, and
$\mathcal Hom_A(F,G)$ is constructible.

## Proof

On a site cover choose a bounded finite free model $P$ of $K$
using [def-weil-site-perfect-complex]. Then
$R\mathcal Hom_A(K,M)=P^\vee\otimes_A^LM$ by
[lem-sf-hom-finite-projective]. Finite sums, shifts and cones of
constructible cohomology sheaves remain constructible by
[thm-constructible-serre]. This proves the local assertion,
which descends on the site. For $F$ concentrated in degree zero the
same model has only one term, giving the last assertion.
