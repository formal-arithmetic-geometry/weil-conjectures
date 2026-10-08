+++
id = "sk-rem-sf-kv-formal"
kind = "section"
title = "What is formal and what is not"
order = 2229
+++
*Remark (sketch).*

Given biduality [sk-prop-sf-biduality-general], the Verdier exchange
[sk-thm-sf-verdier-exchange] has as its adjoint
$Rf^!\cong\mathbb D_X\,Lf^*\,\mathbb D_Y$, and the internal adjunction
$\RHom(A,\mathbb D C)\cong\mathbb D(A\otimes^LC)$ then rewrites
$\RHom(p_Y^*N,Rp_X^!M)$ as $\mathbb D_{X\times Y}(\mathbb D_XM\boxtimes N)$.
So [sk-thm-sf-kunneth-verdier] is *equivalent*, by formal manipulation
inside the package, to the statement that duality commutes with the external
product,

$$
\mathbb D_{X\times Y}(M\boxtimes N)\cong\mathbb D_XM\boxtimes\mathbb D_YN .
$$

What is not formal is that statement itself: at $M=\Lambda_X$, $N=\Lambda_Y$
it reads $\omega_{X\times Y}\cong\omega_X\boxtimes\omega_Y$, which is $\alpha$
with constant coefficients and therefore needs purity, localization and
dévissage as above. For *perfect* $M$, $N$ on *smooth* $X$, $Y$
(of pure dimension) it is formal, by
[sk-thm-sf-dual-perfect] and [sk-prop-sf-dualizable-biduality]; that
perfect case is the base of the induction, not a substitute for it.
