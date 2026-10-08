+++
id = "prop-pod-degree-of-the-pairing"
kind = "theorem"
title = "Degree of the pairing"
order = 2433
tags = ["latex:proposition"]
uses = ["def-coefficient-twists-detailed", "def-pod-derived-poincare-pairing"]
+++
In the Poincare duality conventions of this chapter (the fixed setting), let $\Lambda\in\{A,\mathcal O_E,E,\overline{\mathbf Q}_{\ell}\}$ and let $K\in D^b_{ctf}(X,\Lambda)$ be perfect over $\Lambda_X$. The shift convention $H^r(C[m])=H^{r+m}(C)$ identifies the degree-zero part of the derived pairing $\beta _K$ of Definition 9.17 with the pairings

$$
\langle -,-\rangle _i:\   H_c^i(X,K)\times H^{2d-i}\bigl(X,K^\vee (d)\bigr) \longrightarrow \Lambda \qquad (i\in \mathbf Z).
$$

Before inserting the Tate twist, the same morphism is the line-valued pairing

$$
H_c^i(X,K)\times H^{2d-i}(X,K^\vee ) \longrightarrow \Lambda(-d),
$$

obtained by eliminating the invertible twist $\Lambda _X(d)$ of the second factor through the canonical isomorphism $H^{2d-i}(X,K^\vee (d))\cong H^{2d-i}(X,K^\vee )\otimes _\Lambda \Lambda (d)$ and using the twist inverse.

## Proof

The degree of $\beta _K$ is zero: both the mixed-support cup product and the evaluation are degree-preserving, and the trace $\operatorname {Tr}^{\mathrm{sm}}_{a_X,\Lambda }$ has degree zero on the shifted complex $R\Gamma _c(X,\Lambda _X(d))[2d]$, whose top cohomology sits in degree $2d-2d=0$. Unpacking $H^r(C[m])=H^{r+m}(C)$ in the second variable gives $H^0\bigl(R\Gamma (X,K^\vee (d))[2d]\bigr)=H^{2d}(X,K^\vee (d))$ and, more generally, decomposing into cohomological degrees, the degree-zero part of the pairing pairs $H_c^i(X,K)$ against $H^{-i}\bigl(R\Gamma (X,K^\vee (d))[2d]\bigr)=H^{2d-i}(X,K^\vee (d))$. For the line-valued form, the twist $\Lambda _X(d)=\Lambda _X\otimes _\Lambda \Lambda (d)$ with $\Lambda (d)$ the invertible locally constant rank-one twist sheaf of [def-coefficient-twists-detailed] is eliminated by tensoring the pairing with its twist inverse $\Lambda(-d)$ and using the canonical isomorphisms $\Lambda (d)\otimes _\Lambda \Lambda (-d)\cong \Lambda$: this is the identification of $H^{2d-i}(X,K^\vee (d))$ with $H^{2d-i}(X,K^\vee )\otimes _\Lambda \Lambda (d)$ (by [def-coefficient-twists-detailed], the twist of a complex commutes with the global sections), so the pairing becomes $H_c^i(X,K)\times H^{2d-i}(X,K^\vee )\to \Lambda(-d)$.
