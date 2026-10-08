+++
id = "thm-pod-equivariance-of-the-twisted-pairing"
kind = "theorem"
title = "Equivariance of the twisted pairing"
order = 2434
uses = ["def-pod-derived-poincare-pairing", "def-pod-dual-tate-datum", "def-pur-tate-datum", "def-trf-frobenius-operators", "def-weil-frobenius-detailed", "def-weil-global-geometric-frobenius", "def-weil-weil-sheaf-complex", "lem-fix-weil-operations", "prop-pod-degree-of-the-pairing", "prop-pod-dual-tate-data-compatibility", "thm-pur-weil-equivariance-of-purity-and-trace"]
+++
In the Poincare duality conventions of this chapter (the fixed setting), strict Weil complex with $K$ perfect. With $F_{c,K}$ and $F_{K^\vee (d)}$ the operators of Definition 7.7 formed from $\varphi _K$ and the datum $\varphi _{K^\vee (d)}$ of Definition 9.28, the degreewise pairings satisfy

$$
\bigl\langle F_{c,K}x,\; F_{K^\vee (d)}y\bigr\rangle _i =\langle x,y\rangle _i \qquad \bigl(x\in H_c^i(X,K),\  y\in H^{2d-i}(X,K^\vee (d))\bigr),
$$

where the action on the second factor includes the scalar $q^{-d}$ on $A_X(d)$ and the pairing is the derived Poincare pairing in the form of Proposition 9.21.

## Proof

Step 1: the derived pairing $\beta _K$ of [def-pod-derived-poincare-pairing] is the composite of the mixed-support cup product, the evaluation, and the smooth trace. The mixed-support cup product is induced by the tensor product of sheaves and its $\Gamma _c$-realization, both equivariantly lifted to Weil complexes by [lem-fix-weil-operations], and the same statement applies to the global-sections functors $R\Gamma _c$ and $R\Gamma$ with the data of [def-trf-frobenius-operators]. The evaluation is a morphism of Weil objects by [prop-pod-dual-tate-data-compatibility]. The trace $\operatorname {Tr}^{\mathrm{sm}}_{a_X,A}$ is equivariant by the trace square of [thm-pur-weil-equivariance-of-purity-and-trace], whose source datum carries the twist normalization of the Tate line, [def-pur-tate-datum], and the target datum on $A$ is the canonical datum of [def-weil-weil-sheaf-complex]. Step 2: composing, the tuple

$$
\bigl(R\Gamma _c(X,K),\  R\Gamma (X,K^\vee (d))[2d],\  A\bigr)
$$

carries the Weil data $\varphi _{c,K},\  \varphi _{K^\vee (d)}$, and the canonical datum, and the pairing $\beta _K$ is a morphism of Weil objects from the tensor of the first two to the last, by Step 1 and the compatibility of the tensor product with the data in [lem-fix-weil-operations]. Step 3: on cohomology, in the degree-zero part

$$
\beta _K:\  H_c^i(X,K)\otimes H^{2d-i}\bigl(X,K^\vee (d)\bigr)\to A
$$

of the pairing (the form of [prop-pod-degree-of-the-pairing]), the induced operators are the $F$'s of [def-trf-frobenius-operators]: the operator on the first factor is $F_{c,K}$, and the operator on the second factor is $F_{K^\vee (d)}$, the datum $\varphi _{K^\vee (d)}$ containing the scalar $q^{-d}$ on $A_X(d)$ by [def-pod-dual-tate-datum] and [def-pur-tate-datum]. The morphism property of Step 2 evaluated on the tensor of two vectors gives

$$
\bigl\langle F_{c,K}x,\; F_{K^\vee (d)}y\bigr\rangle _i =F\bigl(\langle x,y\rangle _i\bigr)
$$

with $F$ the global geometric Frobenius of [def-weil-global-geometric-frobenius]; but the target datum is the canonical one, so $F$ acts on $A$ as the identity, by [def-weil-frobenius-detailed] and [def-weil-weil-sheaf-complex], giving the displayed identity.
