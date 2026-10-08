+++
id = "lem-trf-simple-constructible"
kind = "lemma"
title = "Simple constructible sheaves"
order = 2220
+++
Let $X$ be a Noetherian scheme and $\Lambda$ a finite ring. Every
simple object of the abelian category of constructible $\Lambda$-sheaves on
$X_{\Et}$ is of the form $i_{x!}M$, where $x\in X$ is a point with
$\{x\}$ locally closed, $i_x:\operatorname{Spec}\kappa(x)\to X$ is the
induced immersion, and $M$ is a simple finite $\Lambda$-module with a
continuous action of $\operatorname{Gal}(\kappa(x)^{\mathrm{sep}}/\kappa(x))$,
viewed as a sheaf on $\operatorname{Spec}\kappa(x)$. If $X$ is of finite type
over a field, $x$ is a closed point and $i_{x!}=i_{x*}$. In particular a
nonzero lisse sheaf on a scheme of positive dimension is not a finite
extension of simple constructible sheaves.

## Proof

Let $F$ be simple, and let $\eta$ be the generic point of an irreducible
component $V$ of the closure of the support of $F$. Choose an open
$U\subset V$ containing $\eta$, disjoint from the other components, on
which $F|_U$ is locally constant and nonzero, and an open $W\subset X$ with
$W\cap\overline{\operatorname{supp}F}=U$. Extension by zero gives a nonzero
subsheaf $j_{W!}(F|_W)\subset F$, so it equals $F$ and
$\operatorname{supp}F\subset U$. If $U\neq\{\eta\}$, pick a point
$y\in U$ closed in $U$, $y\neq\eta$, and put
$W'=W\setminus\overline{\{y\}}$; then $j_{W'!}(F|_{W'})$ is a nonzero
subsheaf of $F$ (it is nonzero at $\eta$) with zero stalk at $y$, where $F$
is nonzero, contradicting simplicity. Hence $U=\{\eta\}$, so $\{\eta\}$ is
locally closed and $F=i_{\eta!}M$ with $M=i_\eta^*F$. Subsheaves of
$i_{\eta!}M$ are supported in $\{\eta\}$, hence of the form $i_{\eta!}N$ for
a Galois-stable submodule $N\subset M$, so $M$ is simple. Conversely each
such $i_{x!}M$ is simple by the same correspondence. On a scheme of finite
type over a field a locally closed point is closed (Jacobson property). For
the last assertion: a finite extension of punctual sheaves has finite
support, while a nonzero lisse sheaf on a positive-dimensional scheme does
not.
