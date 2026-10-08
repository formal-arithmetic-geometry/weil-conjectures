+++
id = "thm-weil-pbc-finite-level-proetale"
kind = "theorem"
title = "Finite-level pro-etale proper base change"
order = 1325
uses = ["def-weil-pbc-ambient-ringed-exchange", "def-weil-pbc-etale-origin-witness", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-transport-identifies-exchange", "thm-weil-pbc-bounded-below", "thm-weil-pbc-site-comparison"]
+++
Let $\Lambda$ be finite, let $f$ be proper, and let
$K\in\Dplus(X_{\Proet},\Lambda)$ carry an etale-origin witness
[def-weil-pbc-etale-origin-witness] $(L,\alpha)$. Then the pro-etale exchange
map

$$
 g^{-1}Rf_*K\xrightarrow{\sim}Rf'_*g'^{-1}K
$$

is an isomorphism. It is independent of replacing the witness by an
isomorphic witness.

*Source note:* for proper base change on the pro-etale site, see Stacks
Project, Pro-etale Cohomology, Section 61.30
([Tag 09C8](https://stacks.math.columbia.edu/tag/09C8)).

## Proof

The bounded-below theorem of the proper-base-change chapter makes the etale
exchange map for $L$ an isomorphism; the fully faithful comparison of
[thm-weil-pbc-site-comparison] transports it to the pro-etale site, where
[lem-weil-pbc-transport-identifies-exchange] identifies the transported map
with the pro-etale exchange map for $\nu_X^*L$, which is $K$ under the
witness of [def-weil-pbc-etale-origin-witness]. Independence of the witness
follows from the functoriality of the transported map.
