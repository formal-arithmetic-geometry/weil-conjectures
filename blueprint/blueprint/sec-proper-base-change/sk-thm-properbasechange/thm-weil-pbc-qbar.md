+++
id = "thm-weil-pbc-qbar"
kind = "theorem"
title = "Qbar-l proper base change"
order = 1359
uses = ["def-weil-pbc-finite-stage-pair-category", "def-weil-pbc-qbar-category", "def-weil-pbc-scheme-conventions", "prop-weil-pbc-descent-functors", "thm-weil-pbc-finite-extension"]
+++
Let $f:X\to Y$ be proper, let $g:Y'\to Y$ be arbitrary, and let
$K\in\Dbc(X,\Qlb)$. The descended exchange transformation of
[prop-weil-pbc-descent-functors] is an isomorphism
$$
 Lg^*Rf_*K\xrightarrow{\sim}Rf'_*Lg'^*K
 \quad\text{in }\Dbc(Y',\Qlb).
$$
If $K$ is represented by a pair $(E,K_E)$ with $K_E\in\Dbc(X,E)$, this map
is represented after a finite overfield $M$ by the $M$-coefficient exchange
isomorphism of [thm-weil-pbc-finite-extension] applied to $T_{M/E}K_E$. The
result is independent of $E$, $M$, and the representative.

*Source note:* at each finite stage this is Stacks Project, Pro-etale
Cohomology, Theorem 61.30.1 ([Tag
09C9](https://stacks.math.columbia.edu/tag/09C9)), applied with
$\Lambda=\mathcal O_E$: a proper base-change isomorphism for a derived
complete $K$ whose reductions are bounded below and of etale origin. What
the blueprint adds is the statement on the $\Qlb$ coefficient category
$\Dbc(Y',\Qlb)$, obtained by descent from the finite-stage isomorphisms
along the scalar extensions $T_{F/E}$, together with the independence of the
stage and of the representative.

## Proof

The scalar-compatible family of finite-extension exchange maps descends to a
natural transformation by [prop-weil-pbc-descent-functors]; at every finite
stage it is an isomorphism by [thm-weil-pbc-finite-extension], and the
descent formula preserves this property through the common-stage colimit of
[def-weil-pbc-qbar-category]. Independence of the representatives is the
independence statement of [thm-weil-pbc-finite-extension] together with the
equivalence relation of [def-weil-pbc-finite-stage-pair-category].
