+++
id = "prop-pur-affine-line-orientation-uniqueness"
kind = "theorem"
title = "Uniqueness of the global orientation"
order = 1952
tags = ["latex:proposition"]
uses = ["def-pur-conventions", "def-weil-derived-cohomology-sheaves", "def-weil-derived-pullback-tensor-hom", "def-weil-scheme-morphism-properties", "lem-pur-gysin-structure", "thm-pur-affine-line-orientation", "thm-pur-rank-one-local-calculation"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting), let $Y$ and $\kappa(t)$ be as in
[thm-pur-affine-line-orientation]. The restriction of the
homomorphism group to
geometric points is an
injective map

$$
\operatorname{Hom}_{D(Y,\Lambda)}
\bigl(\Lambda_Y,Rs^!\Lambda_{\mathbf A^1_Y}(1)[2]\bigr)
\longrightarrow
\prod_{\bar y\to Y}H^2_{s(\bar y)}(\mathbf A^1_{\bar y},\Lambda(1)),
$$

whose image contains the family with every component $1\in\Lambda$ (by
[thm-pur-rank-one-local-calculation] and the normalization of
[thm-pur-affine-line-orientation]). Consequently
$\operatorname{pur}_s$ is the unique global morphism whose pullback to
every geometric point is the normalized class $1$.

## Proof

Step 1: reduction to sections of a sheaf. By
[lem-pur-gysin-structure], $F:=Rs^!\Lambda_{\mathbf A^1_Y}(1)[2]$ is
concentrated in degree zero with

$$
\Hom_{D(Y,\Lambda)}(\Lambda_Y,F)=H^0(Y,F)=\Gamma\bigl(Y,\mathcal H^0(F)\bigr),
$$

the first equality being the definition of the global sections as
$\operatorname{Hom}$ with the unit object (the tensor–internal-Hom
adjunction of [def-weil-derived-pullback-tensor-hom]) and the
second the degree-zero cohomology of a complex concentrated in one
degree. Step 2: the injectivity. A section $s\in\Gamma(Y,\mathcal H^0(F))$ is determined by its stalks: if all stalks $s_{\bar y}=0$,
then $s=0$, by the stalk criterion for the equality of sheaf
sections on the (small pro-)etale site
([def-weil-derived-cohomology-sheaves]). The map of the statement
is exactly the stalkwise evaluation of the section, hence injective.
Step 3: the image contains $(1)_{\bar y}$. By the normalization in
[thm-pur-affine-line-orientation], the pullback of
$\operatorname{pur}_s$ to $\bar y$ is the class $1$ of
[thm-pur-rank-one-local-calculation] under the canonical
identification of $(Rs^!\Lambda(1)[2])_{\bar y}$ with the support
object at the point (the exactness of the pullback along a geometric
point and [lem-pur-gysin-structure]). Step 4: the uniqueness.
If $\varphi:\Lambda_Y\to F$ is any morphism whose pullbacks are all
$1$, then its section equals the section of $\operatorname{pur}_s$
by Step 2, so $\varphi=\operatorname{pur}_s$.
