+++
id = "prop-weil-pbc-amplification-consequences"
kind = "theorem"
title = "Amplitude containments implied by amplification"
order = 1351
uses = ["def-weil-pbc-adic-coefficient-datum", "def-weil-pbc-cartesian-square", "def-weil-pbc-constructible-direct-image-finiteness", "def-weil-pbc-derived-categories", "def-weil-pbc-finite-level-amplification", "def-weil-pbc-proetale-operations", "lem-weil-pbc-pullback-preserves-bounded-constructible", "prop-weil-pbc-restriction-direct-image"]
tags = ["latex:proposition"]
+++
Let $\square$ be a cartesian square [def-weil-pbc-cartesian-square] with
$\Lambda$-coefficient data as in the adic coefficient datum and suppose that
$\mathrm{AMP}(\square;c)$ of [def-weil-pbc-finite-level-amplification]
holds. Then for every $n\geq1$, with $P_n=A/I^n$, and all $a\leq b$,
$$
 \begin{aligned}
  Rf_*\bigl(D^b_c(X_{\Proet},P_n)^{[a,b]}\bigr)
  &\subset D^b_c(Y_{\Proet},P_n)^{[a,b+c]},\\
  Rf'_*\bigl(D^b_c(X'_{\Proet},P_n)^{[a,b]}\bigr)
  &\subset D^b_c(Y'_{\Proet},P_n)^{[a,b+c]},\\
  Lg_n^*\bigl(D^b_c(Y_{\Proet},P_n)^{[a,b]}\bigr)
  &\subset D^b_c(Y'_{\Proet},P_n)^{[a,b]},\\
  Lg_n'^*\bigl(D^b_c(X_{\Proet},P_n)^{[a,b]}\bigr)
  &\subset D^b_c(X'_{\Proet},P_n)^{[a,b]}.
 \end{aligned}
$$

*Source note:* no Stacks Project entry states these four containments: they
are formal consequences of the predicate of
[def-weil-pbc-finite-level-amplification], whose etale inputs are Lemma
59.92.2 ([Tag 095U](https://stacks.math.columbia.edu/tag/095U), the
amplitude bound $R^qf_*=0$ for $q>2n$ when the fibres have dimension
$\le n$) and Theorem 63.14.5 ([Tag
0GL0](https://stacks.math.columbia.edu/tag/0GL0), constructibility of
$Rf_!$), together with Definition 61.29.1 ([Tag
09C1](https://stacks.math.columbia.edu/tag/09C1)) and Proposition 61.29.7
([Tag 09C7](https://stacks.math.columbia.edu/tag/09C7)) for adic
constructibility; the blueprint adds the assembly of the containments for
the four functors of one square.

## Proof

By [def-weil-pbc-finite-level-amplification] the condition
$\mathrm{AMP}(\square;c)$ consists, for every $n\geq1$, of the finiteness
conditions $\mathrm{FIN}(f,P_n;c)$ and $\mathrm{FIN}(f',P_n;c)$ of
[def-weil-pbc-constructible-direct-image-finiteness] and of the restriction
of the pullbacks $Lg_n^*,Lg_n'^*$ to exact triangulated functors carrying
the class of objects with cohomology in $[a,b]$ into the same class. The
finiteness conditions supply the hypotheses of
[prop-weil-pbc-restriction-direct-image], which therefore yields the first
two displayed containments; the restriction clause is the conclusion of
[lem-weil-pbc-pullback-preserves-bounded-constructible] for the two
coordinates, which yields the last two.
