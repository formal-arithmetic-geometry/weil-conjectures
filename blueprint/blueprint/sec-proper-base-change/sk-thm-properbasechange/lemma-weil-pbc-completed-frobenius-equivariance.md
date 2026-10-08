+++
id = "lemma-weil-pbc-completed-frobenius-equivariance"
kind = "lemma"
title = "Completed proper base change is Frobenius-equivariant"
order = 1340
uses = ["def-weil-pbc-completed-frobenius-structures", "lemma-weil-pbc-frobenius-product-cone-limit", "lemma-weil-pbc-level-map-operator-naturality"]
+++
For every Frobenius-equivariant square and Weil tower datum,

$$
\operatorname{Ex}^{\mathrm{comp}}_{\square,K}\Theta_S
=\Theta_T\Phi_{Y'}
(\operatorname{Ex}^{\mathrm{comp}}_{\square,K}):
\Phi_{Y'}S\longrightarrow T.
$$

If all four Frobenius automorphisms and all pullback/exchange comparisons are
identities, then $\vartheta_n$ is an ordinary compatible endomorphism and
this equation specializes exactly to the operator naturality of the finite
rectangle and its product-cone limit. For nonidentity Frobenius, no
identification of $\Phi_XK_n\to K_n$ with an endomorphism $K_n\to K_n$ is
made.

## Proof

Using the displayed definitions and cancelling $s^{-1}s$ and $t^{-1}t$,
the left side is

$$
tW\Theta_{A,\infty}\Phi_{Y'}(s),
$$

whereas the right side is

$$
t\Theta_{D,\infty}\Phi_{Y'}(W)\Phi_{Y'}(s).
$$

They are equal by the product-cone Frobenius equation. When every
$\Phi_Z$ is the identity, the four formulas defining $\Theta_{Z,n}$ become
the endomorphisms induced from $\vartheta_n$ and the equation just proved is
the fibrewise limit of the equations in operator naturality. This proves
the specialization statement without using it to type the genuine
Frobenius case.
