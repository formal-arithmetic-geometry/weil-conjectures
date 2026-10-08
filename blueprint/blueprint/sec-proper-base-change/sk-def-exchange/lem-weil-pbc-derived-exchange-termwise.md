+++
id = "lem-weil-pbc-derived-exchange-termwise"
kind = "lemma"
title = "The termwise construction of the derived exchange morphism"
order = 1041
uses = ["def-weil-pbc-cartesian-square", "def-weil-pbc-derived-categories", "def-weil-pbc-derived-exchange", "def-weil-pbc-direct-image", "def-weil-pbc-inverse-image", "def-weil-pbc-kinjective-resolutions", "def-weil-pbc-underived-exchange", "prop-weil-pbc-kinjective-resolutions-exist"]
+++
Let $\square$ be a cartesian square
[def-weil-pbc-cartesian-square] and let $K\in\Dplus(X_{\Et})$. If
$K\to I$ is a K-injective resolution
[def-weil-pbc-kinjective-resolutions] of $K$ and $g'^{-1}I\to J$ is a
K-injective resolution of $g'^{-1}I$ on $X'$, then the morphism

$$
 g^{-1}Rf_*K\longrightarrow Rf'_*g'^{-1}K
$$

of the derived category [def-weil-pbc-derived-categories] obtained by
applying the underived exchange morphism
[def-weil-pbc-underived-exchange] $\Ex^0_{\square,I}$ term by term
to $I$ and comparing $g'^{-1}I$ with $J$ is the derived exchange morphism
$\Ex_{\square,K}$ of [def-weil-pbc-derived-exchange].

## Proof

By [def-weil-pbc-derived-exchange] the morphism $\Ex_{\square,K}$ is
the mate, under the derived adjunction $f'^{-1}\dashv Rf'_*$, of the
composite $g'^{-1}\varepsilon_f\circ\theta_\square$ of the identification
$\theta_\square$ of [def-weil-pbc-cartesian-square] with the counit
of the adjunction of [def-weil-pbc-inverse-image]. The termwise construction
applies to $I$ the mate of the same composite in the underived adjunction
$f'^{-1}\dashv f'_*$, namely the underived exchange morphism
$\Ex^0_{\square,I}$ of [def-weil-pbc-underived-exchange]; its source
$g^{-1}Rf_*K$ is computed by $g^{-1}I$ and its target $Rf'_*g'^{-1}K$ by the
K-injective resolution $J$ of $g'^{-1}I$, both resolutions existing by
[prop-weil-pbc-kinjective-resolutions-exist] and being K-injective in the
sense of [def-weil-pbc-kinjective-resolutions]. Since the derived direct
image of [def-weil-pbc-direct-image] is computed by K-injective resolutions,
forming mates commutes with the passage from the underived adjunction to the
derived one, so the two procedures produce the same morphism of the derived
category, namely $\Ex_{\square,K}$ as defined in
[def-weil-pbc-derived-exchange].
