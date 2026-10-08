+++
id = "thm-pod-degreewise-perfectness-over-a-field"
kind = "theorem"
title = "Degreewise perfectness over a field"
order = 2440
uses = ["def-pod-derived-poincare-pairing", "def-pod-perfect-complex-on-x", "def-pod-perfect-point-complex", "def-weil-finite-coefficient-point", "lem-pod-cohomology-of-dual-over-field", "lem-pod-perfect-point-complex-field", "prop-pod-degree-of-the-pairing", "thm-pod-derived-poincare-duality", "thm-pod-point-perfectness"]
+++
In the Poincare duality conventions of this chapter (the fixed setting), fix the field stage $\Lambda \in \{ E,\overline{\mathbf Q}_{\ell }\}$ of the datum (with the finite coefficient groups $H^i_c(X,K)$, $H^i(X,K)$); let $K\in D^b_{ctf}(X,\Lambda )$ be perfect over $\Lambda _X$ in the sense of Definition 9.6, and let $\langle -,-\rangle _i$ denote the degreewise pairings of Proposition 9.21,

$$
\langle -,-\rangle _i:\   H_c^i(X,K)\times H^{2d-i}\bigl(X,K^\vee (d)\bigr)\longrightarrow \Lambda ,
$$

obtained by decomposing the degree-zero part of the derived Poincare pairing $\beta _K$ of Definition 9.17. Then all cohomology spaces in the displays of Proposition 9.21 are finite-dimensional, and each map

$$
H^{2d-i}\bigl(X,K^\vee (d)\bigr) \xrightarrow {\  \sim \  }H_c^i(X,K)^\vee
$$

– the adjoint of $\langle -,-\rangle _i$, the right side being the ordinary dual of a finite-dimensional $\Lambda$-vector space, by Definition 1.50 – is an isomorphism; equivalently each bilinear pairing $\langle -,-\rangle _i$ is perfect, and the line-valued pairing $H_c^i(X,K)\times H^{2d-i}(X,K^\vee )\to \Lambda (-d)$ is perfect degreewise.

## Proof

The derived duality of [thm-pod-derived-poincare-duality] is an isomorphism of perfect point complexes over the field $\Lambda$ (the field-stage case of [thm-pod-point-perfectness]). Apply $H^{-i}$ to both sides. On the right, $H^{-i}(C^\vee )\cong H^i(C)^\vee$ for $C=R\Gamma _c(X,K)$, a bounded complex of finite-dimensional vector spaces (the field-stage definition of perfectness, [def-pod-perfect-point-complex]), hence with bounded finite-dimensional cohomology by [lem-pod-perfect-point-complex-field], by [lem-pod-cohomology-of-dual-over-field]. On the left, $H^{-i}\bigl(R\Gamma (X,K^\vee (d))[2d]\bigr) =H^{2d-i}(X,K^\vee (d))$ by the shift convention. Hence the isomorphism and hence the perfectness of the degreewise pairings, the derived pairing being perfect by [thm-pod-derived-poincare-duality]; the line-valued form follows from the twist elimination of [prop-pod-degree-of-the-pairing].
