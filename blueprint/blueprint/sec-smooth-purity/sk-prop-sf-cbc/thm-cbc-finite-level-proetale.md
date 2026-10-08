+++
id = "thm-cbc-finite-level-proetale"
kind = "theorem"
title = "Finite-level pro-etale compact-support base change"
order = 1648
uses = ["def-cbc-compact-support-square", "def-cbc-exchange-map", "def-weil-pbc-etale-origin-witness", "def-weil-pbc-scheme-conventions", "lem-cbc-proetale-extension-zero-base-change", "lem-cbc-proetale-extension-zero-comparison", "lem-weil-pbc-transport-identifies-exchange", "prop-weil-pbc-comparison-direct-image", "thm-cbc-finite-torsion", "thm-weil-pbc-site-comparison"]
+++
Let $\Lambda$ be finite, let $\square$ be a
compact-support
base-change square with $f$ separated of finite type and
$g:Y'\to Y$ arbitrary, and let
$K\in D^+(X_{\Proet},\Lambda)$ carry an
etale-origin witness
$(L,\alpha)$. Then the pro-etale exchange map

$$
g^{-1}Rf_!K\xrightarrow{\ \sim\ }Rf'_!g'^{-1}K
$$

of [def-cbc-exchange-map] (with the compact-support functors
and exchange map of [def-cbc-exchange-map] transported to the
pro-etale site) is an isomorphism; it is independent of replacing
the witness by an isomorphic one.

## Proof

Choose a compactification $c=(j,p)$ of $f$ with base change
$c'$ as in [def-cbc-compact-support-square]. The etale
statement of [thm-cbc-finite-torsion] applies to the etale
representative $L$: the etale exchange map
$\operatorname{Ex}_!(L)$ is an isomorphism. Transporting it to
the pro-etale site: the fully faithful comparison
$\nu_T^*$ of [thm-weil-pbc-site-comparison] (the interface
`OBL-PBC-SITE-COMPARISON` of the proper-base-change chapter) carries the
direct-image parts by
[lem-weil-pbc-transport-identifies-exchange] (and
[prop-weil-pbc-comparison-direct-image]), and the
extension-by-zero factors by the comparisons
[lem-cbc-proetale-extension-zero-comparison] (etale to
pro-etale) and [lem-cbc-proetale-extension-zero-base-change]
(pro-etale base change); the transported composite is the pro-etale
map of [def-cbc-exchange-map] for $K=\nu_X^*L$. Independence
of the witness follows from the functoriality of the transported map and
the notion of an etale-origin witness of
[def-weil-pbc-etale-origin-witness].
