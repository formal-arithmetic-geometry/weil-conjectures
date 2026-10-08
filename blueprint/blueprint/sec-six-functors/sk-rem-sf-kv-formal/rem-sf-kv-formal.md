+++
id = "rem-sf-kv-formal"
kind = "remark"
title = "Künneth–Verdier is formally duality of external products"
order = 2231
+++
Given biduality [thm-sf-biduality-class], the Verdier exchange
[thm-sf-verdier-exchange] has as its adjoint
$Rf^!\cong\mathbb D_X\,Lf^*\,\mathbb D_Y$, and the internal adjunction
$\RHom(A,\mathbb D C)\cong\mathbb D(A\otimes^LC)$ then rewrites
$\RHom(p_Y^*N,Rp_X^!M)$ as $\mathbb D_{X\times Y}(\mathbb D_XM\boxtimes N)$.
So [thm-trf-kunneth-verdier] is *equivalent*, by formal manipulation
inside the package, to the statement that duality commutes with the external
product,

$$
\mathbb D_{X\times Y}(M\boxtimes N)\cong\mathbb D_XM\boxtimes\mathbb D_YN .
$$

What is not formal is that statement itself: at $M=\Lambda_X$, $N=\Lambda_Y$
it reads $\omega_{X\times Y}\cong\omega_X\boxtimes\omega_Y$, which is $\alpha$
with constant coefficients and therefore needs purity, localization and
dévissage as above. For *perfect* $M$ it is formal, by
[thm-sf-dual-perfect] and [prop-sf-dualizable]; that
perfect case is the base of the induction, not a substitute for it.
