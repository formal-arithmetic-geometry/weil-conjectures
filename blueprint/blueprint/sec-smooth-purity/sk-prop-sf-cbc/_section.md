+++
id = "sk-prop-sf-cbc"
kind = "section"
title = "Compact-support base change"
order = 1517
uses = ["sk-def-av-jacobian"]
lean = ["AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_comp_rightDerivedLowerShriek"]
+++
*Proposition (sketch).*

For $f:X\to Y$ separated of finite type, $g:Y'\to Y$ arbitrary and a
Cartesian square, the exchange transformation
$\operatorname{Ex}_!:Lg^*Rf_!\to Rf'_!Lg'^*$ of [sk-def-sf-exchanges] is an
isomorphism, natural in the coefficient complex and coherent for identity and
pasted squares, *with the following typing only*: (a) at a finite stage
$\Lambda=A_{E,n}$, on all of $D^+(X_{\Et},\Lambda)$, as functors
$D^+(X_{\Et},\Lambda)\to D^+(Y'_{\Et},\Lambda)$ on the small étale site
(thm:cbc-finite-torsion), and on the étale-origin complexes
$\nu_X^*D^+(X_{\Et},\Lambda)$ of the small pro-étale site
(thm:cbc-finite-level-proetale) — hence in $\Dbc(Y',\Lambda)$ whenever
the two sides are bounded constructible; (b) at the stages $\mathcal O_E$,
$E$, $\Qlb$, only on $\Dbc$ of the pro-étale (adic) categories —
derived-complete $\mathcal O_E$-complexes whose reductions are of étale
origin, their rationalizations and the $\Qlb$-colimit, with
$\operatorname{Ex}_!$ the completed exchange
$\operatorname{Ex}^{\mathrm{comp}}_!$ of def:cbc-completed-exchange-map
— where it is an isomorphism in $\Dbc(Y',\Lambda)$, deduced from (a) by
derived limits over the finite reductions and then transported by
rationalization and scalar extension (thm:cbc-complete-proetale,
thm:cbc-finite-extension, thm:cbc-qbar). No assertion is made for
the discrete non-torsion coefficients $\mathcal O_E,E,\Qlb$ on the small
étale site, where $\operatorname{Ex}_!$ is not an isomorphism in general
(for proper $f$ it is the exchange $\operatorname{Ex}_*$ of
[sk-prop-sf-comp-proper], for which [sk-thm-sf-package] (2) records the
same restriction). Whenever $\operatorname{Ex}_!$ is said to be an
isomorphism "at every coefficient stage", this typing is meant.
Chapter 17 (compact-support base change): the stages are
thm:cbc-finite-torsion (finite coefficients, all of $D^+$ of the
étale site), thm:cbc-finite-level-proetale (pro-étale, for objects with
an étale-origin witness), thm:cbc-complete-proetale (derived-complete
coefficients, the completed exchange), thm:cbc-finite-extension
($\Dbc(X,E)$) and thm:cbc-qbar ($\Dbc(X,\Qlb)$).

Uses: `thm-cbc-complete-proetale`, `thm-cbc-finite-extension`, `thm-cbc-finite-level-proetale`, `thm-cbc-finite-torsion`, `thm-cbc-qbar`
