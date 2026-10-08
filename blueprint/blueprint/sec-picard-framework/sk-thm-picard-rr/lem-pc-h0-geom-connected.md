+++
id = "lem-pc-h0-geom-connected"
kind = "lemma"
title = "$H^0=k$ is equivalent to geometric connectedness"
order = 729
uses = ["def-pc-geometrically-irreducible", "def-pc-morphism-conventions", "def-pc-scheme", "lem-pc-coherent-hi", "lem-pc-finite-extension-alg-closed", "lem-sc-flat-base-change-coherent"]
+++
Let $k$ be a field and $X$ a proper
geometrically reduced
scheme over $k$. Then $H^0(X,\mathcal{O}_X)=k$ if and only if $X$ is
geometrically connected.

## Proof

($\Rightarrow$) Let $k'/k$ be a field extension and set
$A_{k'}:=H^0(X_{k'},\mathcal{O}_{X_{k'}})$; by [lem-sc-flat-base-change-coherent]
$A_{k'}=H^0(X,\mathcal{O}_X)\otimes_kk'=k'$. A scheme $Y$ is connected if and
only if every idempotent of $H^0(Y,\mathcal{O}_Y)$ equals $0$ or $1$
(the standard: an idempotent $e$ decomposes $Y=V(e)\sqcup V(1-e)$,
clopen, and conversely a clopen decomposition gives the idempotent
$1$ on one part and $0$ on the other; the two constructions are
inverse). Since $k'$ is a field, $A_{k'}$ has only the trivial
idempotents, so $X_{k'}$ is connected for every $k'$, i.e. $X$ is
geometrically connected.

($\Leftarrow$) Assume $X$ is geometrically connected. Put
$\Omega=\bar k$; $X_\Omega$ is connected and (geometrically reduced,
hence) reduced. By [lem-sc-flat-base-change-coherent],
$H^0(X_\Omega,\mathcal{O}_{X_\Omega})=H^0(X,\mathcal{O}_X)\otimes_k\Omega$, so by
[lem-pc-coherent-hi] (proper $X_\Omega$ over the field $\Omega$)
it is a finite $\Omega$-algebra; it is reduced (a submodule-statement:
$X_\Omega$ is reduced, so a section of $\mathcal{O}$ with $f^n=0$ for some
$n$ is nilpotent in every local ring, hence zero) and has no
nontrivial idempotents (connectedness), hence it is a finite product
of finite field extensions of $\Omega$ with exactly one factor: it is a
finite field extension of $\Omega$; by
[lem-pc-finite-extension-alg-closed] it equals $\Omega$. Thus
$H^0(X,\mathcal{O}_X)\otimes_k\Omega=\Omega$, whence
$H^0(X,\mathcal{O}_X)=k$ (finite type over $k$, its $\Omega$-dimension is
$1$).
