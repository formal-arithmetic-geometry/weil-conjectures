+++
id = "lem-pod-point-dualizing-complex"
kind = "lemma"
title = "Dualizing complex of the point"
order = 2247
uses = ["def-pod-conventions", "def-pod-perfect-point-complex", "def-weil-derived-pullback-tensor-hom", "def-weil-exceptional-inverse-image", "def-weil-finite-coefficient-point", "def-weil-geometric-hypotheses"]
+++
In the Poincare duality conventions of this chapter (the fixed setting),
the exceptional inverse image of the identity is the identity functor,

$$
\omega_{s,\Lambda}=Ra_s^!\Lambda\cong\Lambda_s,
$$

and, for every object $C$ of the
category at the point,

$$
D_sC:=R\mathcal Hom_s\bigl(C,\omega_{s,\Lambda}\bigr)\cong C^\vee.
$$

## Proof

By the construction of the exceptional inverse image of [def-weil-exceptional-inverse-image], $Rf^!$ is the right adjoint
of $Rf_!$; for $f=\operatorname{id}_s$ the functor $Rf_!$ is the
identity, whose right adjoint is the identity, so
$Ra_s^!\Lambda\cong\Lambda_s$. The displayed identification of
$D_s$ is then the definition of $C^\vee$ in
[def-pod-perfect-point-complex], $R\mathcal Hom$ at the point
being computed over the coefficient ring by
[def-weil-derived-pullback-tensor-hom].
