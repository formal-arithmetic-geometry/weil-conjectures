+++
id = "lem-sc-jacobian-unique"
kind = "lemma"
title = "Uniqueness of the Jacobian"
order = 852
uses = ["def-sc-general-curve", "def-sc-jacobian"]
+++
Let $C$ be a geometrically integral smooth
projective curve over $k$ and let $(J,\varphi)$ and $(J',\varphi')$ be
two Jacobians of $C$. Then there is a
unique isomorphism $u:J\to J'$ of $k$-group schemes such that
$\varphi'=h_u\circ\varphi$.

## Proof

Both $(J,\varphi)$ and $(J',\varphi')$ are representing objects
of the functor $\operatorname{Pic}^0_{C/k}$
([def-sc-jacobian]), so
$\psi:=\varphi'\circ\varphi^{-1}:h_J\to h_{J'}$ is an
isomorphism of functors. Evaluating $\psi$ on $J$ at
$\mathrm{id}_J\in h_J(J)$ gives a morphism $u:J\to J'$, and
naturality of $\psi$ shows that $\psi_T:h_J(T)\to h_{J'}(T)$ is
$f\mapsto u\circ f$ for every $k$-scheme $T$, i.e. $\psi=h_u$ (Yoneda's lemma for the functor of points,
*reference: Stacks Project, Categories, Section 4.3,
[Tag 001L](https://stacks.math.columbia.edu/tag/001L)*).
Hence $h_u=\varphi'\circ\varphi^{-1}$, that is
$\varphi'=h_u\circ\varphi$, and $u$ is an isomorphism because
$h_u=\psi$ is one. If $v:J\to J'$ satisfies
$\varphi'=h_v\circ\varphi$, then $h_v=h_u$, so $v=u$; the
isomorphism $u$ is therefore unique. Finally $u$ is a
homomorphism of $k$-group schemes, because $h_u=\psi$ is a
morphism of group-valued functors, i.e. each $\psi_T$ is a group
homomorphism.
