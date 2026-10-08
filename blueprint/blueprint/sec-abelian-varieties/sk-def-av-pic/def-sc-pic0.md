+++
id = "def-sc-pic0"
kind = "definition"
title = "Degree and $\\operatorname{Pic}^0$"
lean = ["AlgebraicGeometry.Scheme.Hom.picZero"]
order = 445
uses = ["def-sc-curves", "def-sc-divisor", "def-sc-picard-group"]
+++
Let $C$ be a proper smooth connected curve over
algebraically closed $k$. The *degree* is the homomorphism

$$
\deg:\operatorname{Pic}(C)\to\mathbf Z,\qquad
\deg[\mathcal O(D)]=\deg D,
$$

of the divisor class group of [def-sc-divisor], transported
across the identification $\operatorname{Cl}(C)\cong \operatorname{Pic}(C)$ of [lem-sc-divisor-class-curve]; it
sends the class of a $k$-rational point
to $1$. That it is well defined, i.e. that it vanishes on
principal divisors, is [lem-sc-deg-principal-zero], and it is
not part of the definition. Put

$$
\operatorname{Pic}^0(C):=\ker(\deg).
$$
