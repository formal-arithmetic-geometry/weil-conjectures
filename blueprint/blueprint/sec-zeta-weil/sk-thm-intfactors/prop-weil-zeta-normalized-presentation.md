+++
id = "prop-weil-zeta-normalized-presentation"
kind = "theorem"
title = "The normalized reduced integral presentation exists and is unique"
order = 2903
tags = ["latex:proposition"]
uses = ["def-weil-normalized-integral-fraction", "prop-rational-descent", "prop-weil-integral-rational-series", "prop-weil-zeta-integral-rational"]
+++
In the situation of [prop-rational-descent], the point-count zeta
series has a unique
normalized reduced
integral presentation: there are unique $A,B\in\mathbf Z[T]$ with
$A(0)=B(0)=1$, $\gcd(A,B)=1$ in $\mathbf Q[T]$, and
$Z(X_0,T)=A(T)/B(T)$.

## Proof

By [prop-weil-zeta-integral-rational] the series lies in
$1+T\mathbf Z[[T]]\cap\mathbf Q(T)$, and
[prop-weil-integral-rational-series] applied to it supplies the
existence and uniqueness of the normalized reduced integral presentation
of [def-weil-normalized-integral-fraction].
