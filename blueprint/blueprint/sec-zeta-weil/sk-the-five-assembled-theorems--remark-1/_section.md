+++
id = "sk-the-five-assembled-theorems--remark-1"
kind = "section"
title = "Remark"
order = 2938
+++
*Remark (sketch).*

*Where this feeds.* This layer is the last one of the blueprint: its
inputs are the trace formula, Poincaré duality and the weight estimate, and
its output is the five statements [sk-thm-weil1]–[sk-thm-weil5]. In the
compiled blueprint the layer is carried by
`16_zeta_linear_algebra.tex` (the linear algebra:
`def-zl-frobenius-trace-series`,
`lem-zl-log-det-identity`,
`lem-zl-euler-product-identity`,
`thm-zl-lefschetz-weil-identity`,
`thm-weil-final-functional-equation`,
`sk-thm-rh`) and by
`18_final_weil_statements.tex` (the assembly:
`prop-every-iterate-trace`, `prop-trace-determinant`,
`prop-euler-product`, `prop-weil-rationality-criterion`,
`prop-rational-descent`, `prop-weight-purity-roots`,
`prop-weight-separation`, `prop-duality-reciprocity`,
`prop-functional-equation`, `prop-weil-betti-comparison`,
`thm-weil-realization-independence`,
`thm-weil-final-rationality`, `thm-weil-final-integrality`,
`thm-weil-final-rh`, `thm-weil-final-betti`,
`thm-weil-final-functional-equation`).

*The one structural point.* The coefficients of $Z$ are integral
*by the Euler product* ([sk-prop-euler]; the exponential definition
alone only gives rational coefficients), while
the factorization is $\ell$-adic *by construction* (one chosen $\ell$,
[sk-thm-tracetodeterminant]). The two meet exactly twice: in the
rationality descent of [sk-thm-rationality], where integrality of the
coefficients propagates the Hankel rank bound from $\Ql$ to $\Q$, and in the
realization-independence of [sk-thm-intfactors], where integrality of the
coefficients enters once more through Fatou's lemma, which produces the
integral presentation $Z=A/B$ and with it the integrality of the reciprocal
roots. Every step that may split
into very many statements is marked qualitatively above.
