+++
id = "lem-sc-global-functions"
kind = "lemma"
title = "Global functions on a proper curve"
order = 1019
uses = ["def-sc-curves", "lem-sc-morphism-from-function", "lem-sc-proper-affine-finite"]
+++
Let $k$ be algebraically closed and let $C$ be a
proper connected curve over $k$. Then

$$
H^0(C,\mathcal O_C)=k.
$$

## Proof

A global function $f\in H^0(C,\mathcal O_C)\setminus k$ would, by
[lem-sc-morphism-from-function], define a morphism
$C\to\mathbf A^1_k$ whose image is proper (the image of a proper
scheme in a separated finite-type target is proper) and affine, hence
finite by [lem-sc-proper-affine-finite]; but $C$ is connected,
so the image is a single point, a $k$-point (the closed points of a
finite-type $k$-scheme are $k$-valued for $k$ algebraically
closed), and $f$ is constant, i.e. $f\in k$, a contradiction.
