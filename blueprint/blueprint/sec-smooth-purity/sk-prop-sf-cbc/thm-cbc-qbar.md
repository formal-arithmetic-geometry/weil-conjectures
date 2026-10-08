+++
id = "thm-cbc-qbar"
kind = "theorem"
title = "$\\Qlb$ compact-support base change"
order = 1645
uses = ["def-weil-pbc-qbar-category", "def-weil-pbc-scheme-conventions", "lem-cbc-extension-zero-projection-formula", "lem-weil-compact-support-finite-field-independence", "prop-weil-pbc-descent-functors", "prop-weil-pbc-scalar-extension", "thm-cbc-finite-extension", "thm-weil-pbc-idempotent-complete-triangulation"]
+++
Let $f:X\to Y$ be separated of finite type, $g:Y'\to Y$ arbitrary
and $K\in\Dbc(X,\Qlb)$, with the finite-level hypotheses of
[thm-cbc-finite-extension] at every finite stage. The
descended exchange transformation of
[prop-weil-pbc-descent-functors] is an isomorphism

$$
Lg^*Rf_!K\xrightarrow{\ \sim\ }Rf'_!Lg'^*K
\quad\text{in }\Dbc(Y',\Qlb).
$$

If $K$ is represented by a pair $(E,K_E)$ with
$K_E\in\Dbc(X,E)$, the map is represented
after a finite overfield $M$ by the $M$-coefficient isomorphism of
[thm-cbc-finite-extension] applied to $T_{M/E}K_E$; the result
is independent of $E$, $M$, and the representative.

## Proof

The scalar-extension compatibilities for the functors $Rf_!$ and
$Lg^*$ hold: for the direct image factor, scalar extension
commutes with $Rp_*$ of the proper $p$ by
[prop-weil-pbc-scalar-extension], and with $j_!$ by the
projection formula [lem-cbc-extension-zero-projection-formula]
(whose scalar-extension instance is
$F\otimes^L_{\mathcal O_E}j_!K\cong j_!(F\otimes^L_{\mathcal O_E}K)$ for a finite field $F/E$,
as $j^*$ of the constant coefficient is the restriction);
hence the family $(Rf_{!,E})_E$ with the exchange
transformations descends by
[prop-weil-pbc-descent-functors], and at every finite stage it
is an isomorphism by [thm-cbc-finite-extension]. The common
stage colimit of [def-weil-pbc-qbar-category], triangulated and
idempotent complete by
[thm-weil-pbc-idempotent-complete-triangulation], preserves the
isomorphism, giving the assertion, with the stated independence as
in [thm-cbc-finite-extension] and [lem-weil-compact-support-finite-field-independence].
