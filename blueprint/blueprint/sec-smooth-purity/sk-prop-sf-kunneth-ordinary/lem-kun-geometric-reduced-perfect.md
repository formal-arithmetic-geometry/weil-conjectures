+++
id = "lem-kun-geometric-reduced-perfect"
kind = "lemma"
title = "Geometric reducedness over a perfect field"
order = 1730
uses = ["def-weil-pbc-scheme-conventions"]
+++
Let $X$ be a reduced scheme of finite type over a perfect field
$K$. For every field extension $L/K$, the scheme $X_L$ is
reduced. Consequently $X\to\Spec(K)$ is flat and of finite
presentation and has geometrically reduced fibres.

## Proof

Reducedness is local on the target, so let $X=\Spec(A)$ with $A$ a
reduced finitely generated $K$-algebra; then
$X_L=\Spec(A\otimes_KL)$. The diagonal map
$A\to\prod_{\mathfrak p}A/\mathfrak p$, the product running over the
finitely many minimal primes, is injective, and $K\to L$ is flat, so
$A\otimes_KL\to\prod_{\mathfrak p}(A/\mathfrak p\otimes_KL)$ is
injective; a subring of a reduced ring is reduced, so it suffices to
treat the case where $A$ is a domain.
Let then $A$ be a domain with fraction field $F$. The extension
$F/K$ is a finitely generated field extension of the perfect field
$K$, hence separable; for a separable field extension $F/K$ and any
field extension $L/K$ the tensor product $F\otimes_KL$ is reduced
(the standard criterion for separable extensions: the nilradical of
$F\otimes_KL$ is killed by the separable degree, which is a unit in
characteristic $0$ and divides a $p$-power only for inseparable
extensions). Since $A\otimes_KL\subseteq F\otimes_KL$ by flatness
of $K\to L$, the ring $A\otimes_KL$ is reduced. Finally
$X\to\Spec(K)$ is flat (every module over a field is flat) and of
finite presentation (as $A$ is a finitely generated $K$-algebra),
and its fibres are the reduced schemes $X_L$ just described.
