+++
id = "thm-weil-pbc-site-comparison"
kind = "theorem"
title = "Bounded-below site comparison"
order = 1286
uses = ["def-weil-pbc-proetale-modules", "def-weil-pbc-site-comparison-morphism", "prop-weil-pbc-kinjective-resolutions-exist", "prop-weil-pbc-site-comparison-finite-level"]
+++
For finite $\Lambda$, the inverse image of the comparison morphism of
[def-weil-pbc-site-comparison-morphism] is fully faithful on bounded-below
complexes of finite-coefficient module sheaves:

$$
 \nu_T^*:\Dplus(T_{\Et},\Lambda)
 \longrightarrow\Dplus(T_{\Proet},\Lambda),
 \qquad \operatorname{id}\xrightarrow{\sim}R\nu_{T,*}\nu_T^*.
$$

## Proof

Represent $K$ by a bounded-below complex $I^\bullet$ of injective module
sheaves. The exactness assertion of
[prop-weil-pbc-site-comparison-finite-level] shows that $\nu_T^*I^\bullet$
represents $\nu_T^*K$. Each of its terms is acyclic for $\nu_{T,*}$ by the
same proposition. The bounded-below acyclic-resolution calculation in
ordinary homological algebra therefore gives

$$
 R\nu_{T,*}(\nu_T^*K)\simeq
 \nu_{T,*}(\nu_T^*I^\bullet).
$$

More explicitly, resolve $\nu_T^*I^\bullet$ by a Cartan--Eilenberg injective
double complex before applying $\nu_{T,*}$. Its column spectral sequence has
$E_1^{p,q}=R^q\nu_{T,*}(\nu_T^*I^p)$; only $q=0$ survives, and its $d_1$
differential is the differential of $\nu_{T,*}\nu_T^*I^\bullet$. Its next
page is thus the cohomology of that complex, not the individual terms $I^p$.
Boundedness below makes each total degree finite in this calculation.

The underived unit is an isomorphism on every $I^p$, by
[prop-weil-pbc-site-comparison-finite-level], and commutes with its
differentials by naturality. It identifies $I^\bullet$ with
$\nu_{T,*}\nu_T^*I^\bullet$. Under the displayed acyclic-resolution
identification, this map is the derived unit for
[def-weil-pbc-site-comparison-morphism]. Hence $K\to R\nu_{T,*}\nu_T^*K$ is a
natural isomorphism. For bounded-below $K,L$, derived adjunction now gives

$$
 \operatorname{Hom}\bigl(\nu_T^*K,\nu_T^*L\bigr)
 \cong\operatorname{Hom}\bigl(K,R\nu_{T,*}\nu_T^*L\bigr)
 \cong\operatorname{Hom}(K,L),
$$

with the second identification induced by that unit. This proves full
faithfulness. The finite-level proposition used here has already established
its geometric acyclicity input by the two finite-cover limits above.
