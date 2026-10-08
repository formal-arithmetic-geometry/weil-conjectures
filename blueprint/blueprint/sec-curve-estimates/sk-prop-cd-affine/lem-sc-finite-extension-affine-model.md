+++
id = "lem-sc-finite-extension-affine-model"
kind = "lemma"
title = "An affine curve model for a finite extension"
order = 1016
uses = ["def-fin-normalization-extension", "def-sc-curves", "def-sc-function-field", "def-weil-pbc-scheme-conventions", "lem-fin-normalization-extension-finite", "lem-sc-normal-dim1-dvr"]
+++
Let $C/k$ be a smooth integral affine
connected curve over algebraically closed $k$,
and let $L/k(C)$ be finite, with function field as in
[def-sc-function-field].
The normalization
$h:C'\to C$ in $L$ is a
finite morphism
from a smooth integral affine connected curve with function field $L$.

## Proof

By [lem-fin-normalization-extension-finite] the integral
closure $B'$ of the affine coordinate ring $B$ in $L$
is finite over $B$. It is a normal domain. Every element
of $L$ becomes integral over $B$ after multiplication by a
nonzero element of $B$, by clearing the coefficients of its
algebraic equation; hence $\operatorname{Frac}(B')=L$.
The construction of [def-fin-normalization-extension]
gives $C'=\operatorname{Spec}B'$. Integral extensions preserve
dimension, so $C'$ has dimension one. Its local rings at
closed points are regular by [lem-sc-normal-dim1-dvr];
at the generic point its local ring is a field.
A regular scheme of finite type over the perfect field $k$
is smooth. This last local algebra criterion is
[Stacks Project,
Tag 00TV](https://stacks.math.columbia.edu/tag/00TV), applied to its essentially finite-type local rings.
This proves the assertion.
