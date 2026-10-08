+++
id = "lem-sc-finite-flat-surj-points"
kind = "lemma"
title = "Finite flat surjections are surjective on $k$-points"
order = 571
uses = ["lem-sc-finite-nonempty-point"]
+++
Let $k$ be algebraically closed and $f:X\to Y$ a finite flat
surjective morphism of schemes of finite type over $k$. Then
$f(X(k))=Y(k)$.

## Proof

Let $y\in Y(k)$. The fibre $X_y=X\times_Yy$ is nonempty
(surjectivity), finite and flat over $k$, hence a nonempty finite
$k$-scheme, which has a $k$-point by
[lem-sc-finite-nonempty-point]; such a point is an
$x\in X(k)$ with $f(x)=y$.
