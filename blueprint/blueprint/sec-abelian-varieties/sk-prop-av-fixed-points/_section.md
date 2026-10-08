+++
id = "sk-prop-av-fixed-points"
kind = "section"
title = "Fixed points of $p$-linear maps are finite"
lean = ["LinearMap.Frobenius.finite_fixedPoints", "LinearMap.Frobenius.natCard_fixedPoints_le"]
order = 562
uses = ["sk-def-av"]
+++
*Proposition (sketch).*

Let $k$ be a field of characteristic $p>0$, $V$ a finite-dimensional
$k$-vector space and $F:V\to V$ a $p$-linear endomorphism
($F(\lambda v)=\lambda^pF(v)$, $F(v+w)=F(v)+F(w)$). Then
$V^F=\{v:F(v)=v\}$ is a finite $\F_p$-vector space of dimension
$\le\dim_kV$.

## Proof

$V^F=\ker(F-1)$ is an $\F_p$-vector space. If $v_1,\dots,v_r\in V^F$
were $\F_p$-independent with a shortest $k$-linear dependence
$\sum_i\lambda_iv_i=0$, applying $F$ and subtracting gives a strictly
shorter dependence
$\sum_{i\ge2}\bigl((\lambda_i/\lambda_1)-(\lambda_i/\lambda_1)^p\bigr)v_i=0$;
minimality forces $\lambda_i/\lambda_1\in\F_p$, contradicting
$\F_p$-independence. Hence $r\le\dim_kV$.

Uses: [sk-def-av]
