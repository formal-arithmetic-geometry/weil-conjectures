+++
id = "lem-weil-pbc-transport-identifies-exchange"
kind = "lemma"
title = "Transport identifies the exchange map"
order = 1324
uses = ["def-weil-pbc-ambient-ringed-exchange", "def-weil-pbc-cartesian-square", "def-weil-pbc-derived-exchange", "def-weil-pbc-site-comparison-morphism", "lem-weil-pbc-comparison-pullback", "prop-weil-pbc-comparison-direct-image"]
+++
For a cartesian square [def-weil-pbc-cartesian-square] and
$L\in\Dplus(X_{\Et},\Lambda)$, use the natural comparison isomorphisms

$$
 \nu_{X'}^*g'_{\Et}{}^{-1}\simeq
 g'_{\Proet}{}^{-1}\nu_X^*,
 \qquad
 \nu_Y^*Rf_{\Et,*}L\simeq Rf_{\Proet,*}\nu_X^*L,
$$

and their analogues for the other sides. Conjugating the etale exchange map
[def-weil-pbc-derived-exchange] by these isomorphisms gives the pro-etale
unit--counit exchange map

$$
 g_{\Proet}^{-1}Rf_{\Proet,*}\nu_X^*L
 \longrightarrow
 Rf'_{\Proet,*}g_{\Proet}'{}^{-1}\nu_X^*L
$$

of [def-weil-pbc-ambient-ringed-exchange].

## Proof

Expanding the unit--$\theta_\square$--counit composite of
[def-weil-pbc-derived-exchange] and conjugating each arrow through the
comparison isomorphisms of [lem-weil-pbc-comparison-pullback] and
[prop-weil-pbc-comparison-direct-image] gives exactly the mate of the ambient
ringed exchange; naturality of the two comparison adjunctions makes the
resulting square commute.
