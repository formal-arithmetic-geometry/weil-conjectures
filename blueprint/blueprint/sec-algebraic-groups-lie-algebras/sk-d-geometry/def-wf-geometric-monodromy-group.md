+++
id = "def-wf-geometric-monodromy-group"
kind = "definition"
title = "Geometric monodromy group"
order = 2478
uses = ["def-sc-general-linear-group", "def-wf-fundamental-representation", "def-wf-weil-group"]
+++
Let $\Pi=\pi_1(X,\bar x)$ be the geometric subgroup of the
Weil group and let
$\rho:W(X_0)\to\operatorname{GL}(V)$ be the representation attached to
a lisse Weil sheaf. The *geometric monodromy group* is the closed
linear algebraic subgroup

$$
H_{\mathrm{geom}}=\overline{\rho(\Pi)}^{\,\mathrm{Zar}}
\subseteq\operatorname{GL}(V).
$$

The closure is taken in the Zariski topology of the affine algebraic
group
$\operatorname{GL}(V)=\operatorname{Spec} \overline{\mathbf Q}_\ell[x_{ij},\det(x)^{-1}]$ of [def-sc-general-linear-group], not in the ambient
affine space of all matrices. Equivalently it is the common zero locus
in $\operatorname{GL}(V)$ of the regular functions vanishing on
$\rho(\Pi)$. That this closure is a subgroup is
[lem-wf-zariski-closure-subgroup].
