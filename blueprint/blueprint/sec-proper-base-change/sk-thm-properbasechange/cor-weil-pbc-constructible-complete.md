+++
id = "cor-weil-pbc-constructible-complete"
kind = "theorem"
title = "Constructible complete proper base change"
order = 1356
uses = ["def-weil-pbc-bounded-constructible-complete", "prop-weil-pbc-preservation-constructible", "thm-weil-pbc-complete-proetale"]
tags = ["latex:corollary"]
+++
Under the hypotheses of [prop-weil-pbc-preservation-constructible], the
theorem [thm-weil-pbc-complete-proetale] restricts to a natural isomorphism
of ordinary triangulated functors
$$
 Lg^*_{\mathrm{comp}}Rf_*K
 \xrightarrow{\sim}Rf'_*Lg'^*_{\mathrm{comp}}K
 \quad\text{in }\Dbc(Y'_{\Proet},A)
$$
for every $K\in\Dbc(X_{\Proet},A)$.

*Source note:* the isomorphism is Stacks Project, Pro-etale Cohomology,
Theorem 61.30.1 ([Tag 09C9](https://stacks.math.columbia.edu/tag/09C9)) with
$K$ satisfying its conditions, and the category $\Dbc(T_{\Proet},A)$ is that
of Definition 61.29.1 ([Tag
09C1](https://stacks.math.columbia.edu/tag/09C1)); the blueprint adds the
restriction of the tower-level theorem to $\Dbc(X_{\Proet},A)$, with the
amplitude bookkeeping proved in
[prop-weil-pbc-preservation-constructible].

## Proof

The isomorphism of [thm-weil-pbc-complete-proetale] exists for every derived
complete $K$ with compatible witnesses; the preservation proposition
[prop-weil-pbc-preservation-constructible] shows that all four displayed
objects lie in the bounded constructible complete category of
[def-weil-pbc-bounded-constructible-complete], so the isomorphism lands
there.
