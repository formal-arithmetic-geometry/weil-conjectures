+++
id = "prop-weil-zeta-integral-rational"
kind = "theorem"
title = "The zeta series is integral and rational"
order = 2892
tags = ["latex:proposition"]
uses = ["def-weil-point-counts-zeta", "prop-euler-product", "prop-rational-descent"]
+++
In the situation of [prop-rational-descent], the
point-count zeta series satisfies

$$
Z(X_0,T)\in1+T\mathbf Z[[T]]\cap\mathbf Q(T).
$$

## Proof

In the situation of [prop-rational-descent] the assumed closed-point
product is the identity of [prop-euler-product], so the
[def-weil-point-counts-zeta] series $Z(X_0,T)$ lies in
$1+T\mathbf Z[[T]]$; by [prop-rational-descent] it also lies in
$\mathbf Q(T)$. This is the assertion.
