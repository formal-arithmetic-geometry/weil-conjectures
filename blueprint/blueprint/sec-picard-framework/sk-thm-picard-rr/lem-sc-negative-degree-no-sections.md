+++
id = "lem-sc-negative-degree-no-sections"
kind = "lemma"
title = "Line bundles of negative degree"
order = 716
uses = ["def-sc-pic0", "lem-sc-deg-principal-zero", "lem-sc-line-bundle-rational-section"]
+++
Let $C$ be a proper smooth curve over an algebraically closed
field $k$, and $\mathcal M$ a line bundle on $C$ with
$\deg\mathcal M<0$ ([def-sc-pic0]). Then
$H^0(C,\mathcal M)=0$.

## Proof

A section $s\neq0$ gives
$\mathcal M\cong\mathcal O(\operatorname{div}s)$ with
$\operatorname{div}s$ effective by
[lem-sc-line-bundle-rational-section], so
$\deg\mathcal M=\deg\operatorname{div}s\geq0$, the degree being
well defined by [lem-sc-deg-principal-zero]; contradiction.
