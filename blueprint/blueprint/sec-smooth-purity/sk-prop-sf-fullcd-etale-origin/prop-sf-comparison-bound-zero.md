+++
id = "prop-sf-comparison-bound-zero"
kind = "theorem"
title = "The comparison bound on coefficients of étale origin is $M=0$"
order = 1797
tags = ["latex:proposition"]
uses = ["def-sf-fullcd-used-class", "def-weil-full-cohomological-dimension", "def-weil-pbc-etale-sheaves", "def-weil-pbc-proetale-modules", "def-weil-pbc-proetale-site", "def-weil-pbc-site-comparison-morphism", "lem-sf-proetale-constructible-origin", "thm-sf-fullcd-etale-origin", "thm-sp-grothendieck"]
+++
Let $X$ be a scheme and let $\nu_X:X_{\Proet}\to X_{\Et}$ be the comparison
morphism of [def-weil-pbc-site-comparison-morphism], the coefficient ring
being $A$. Let $G$ be a sheaf of $A$-modules on the small étale site
$X_{\Et}$, in the sense of [def-weil-pbc-etale-sheaves]; *no*
constructibility hypothesis is imposed on $G$. Then the adjunction map

$$
G\longrightarrow\nu_{X,*}\nu_X^*G
$$

is an isomorphism, and consequently

$$
R^q\nu_{X,*}\bigl(\nu_X^*G\bigr)=0\qquad(q>0).
$$

Thus on the sheaves of étale origin – equivalently, by
[lem-sf-proetale-constructible-origin], on the coefficient sheaves of the
blueprint's class [def-sf-fullcd-used-class] – the vanishing degree of
the comparison direct image is bounded by $M=0$, independently of the
dimension of $X$ and of any constructibility of $G$.
[thm-sf-fullcd-etale-origin] is the form of this statement that the
chapter consumes: there the bound read off for the condition
[def-weil-full-cohomological-dimension] is $2d$, the $2d$ being the
étale direction of the Leray spectral sequence of
[thm-sp-grothendieck] and not the comparison bound, which is $0$.

## Proof

The two inputs are Bhatt–Scholze, Lemma 5.1.1 and Corollary 5.1.6 of
[arXiv:1309.1198v2](https://arxiv.org/html/1309.1198v2), quoted verbatim in
Section 16.1 of the audit ledger; both are stated for an arbitrary scheme and
an arbitrary sheaf, respectively bounded-below complex, on the small étale
site, so a sheaf of $A$-modules on $X_{\Et}$ in the sense of
[def-weil-pbc-etale-sheaves] is covered verbatim. By Lemma 5.1.1, for
$G\in\Sh(X_{\Et})$ and an affine pro-étale $U=\lim_iU_i$ one has
$\nu_X^*G(U)=\colim_iG(U_i)$, the presheaf so defined being a sheaf; by
Lemma 5.1.2 the pullback $\nu_X^*$ is fully faithful, with essential image
exactly those sheaves $F$ on $X_{\Proet}$ whose values on $U=\lim_iU_i$
are the filtered colimits of their values on the $U_i$. The sheaf
$\nu_X^*G$ lies in that essential image, so
$\nu_X^*\nu_{X,*}\nu_X^*G\to\nu_X^*G$ is an isomorphism; applying the fully
faithful $\nu_X^*$ to the two maps $G\to\nu_{X,*}\nu_X^*G$ and
$\nu_{X,*}\nu_X^*G\to G$ that this isomorphism exhibits shows that the
adjunction map $G\to\nu_{X,*}\nu_X^*G$ is an isomorphism in
$\Sh(X_{\Et},A)$. Corollary 5.1.6 is the derived form of the same identity:
$K\to R\nu_{X,*}\nu_X^*K$ is an equivalence for every
$K\in D^+(X_{\Et})$. Taking $K=G$ concentrated in degree zero and passing
to cohomology sheaves gives
$R^q\nu_{X,*}\nu_X^*G=\mathcal H^q(R\nu_{X,*}\nu_X^*G)=0$ for every $q>0$,
which is the displayed vanishing. The identification of the class of étale
origin with the coefficient class [def-sf-fullcd-used-class] is
[lem-sf-proetale-constructible-origin], and the passage from this bound to
the bound $2d$ of [thm-sf-fullcd-etale-origin] in the form of
[def-weil-full-cohomological-dimension] is through the Leray spectral
sequence of [thm-sp-grothendieck], whose $p$-direction is bounded by
$2d$ on the étale site.
