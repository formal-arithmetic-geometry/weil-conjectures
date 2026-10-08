+++
id = "def-weil-pbc-projection-formula-arrows"
kind = "definition"
title = "Projection-formula arrows"
order = 1264
uses = ["def-weil-pbc-strict-perfect-coefficient-package"]
+++
For a morphism of ringed topoi $h:\mathcal T\to\mathcal S$, an object
$E\in D(\mathcal T,\Lambda)$, and a strict-perfect package $F^\bullet$ on
$\mathcal S$, define

$$
\pi_{h,E,F}:Rh_*E\otimes^L_\Lambda F^\bullet
\longrightarrow Rh_*(E\otimes^L_\Lambda Lh^*F^\bullet)
$$

to be adjoint to

$$
Lh^*(Rh_*E\otimes^LF^\bullet)
\simeq Lh^*Rh_*E\otimes^LLh^*F^\bullet
\xrightarrow{\epsilon_E\otimes1}
E\otimes^LLh^*F^\bullet.
$$

For $F^r=\Lambda^{N_r}$, let $\rho_r$ be the inverse of the finite-sum
identification

$$
(Rh_*E)^{N_r}\xrightarrow{\pi_r}Rh_*(E^{N_r}).
$$

For a projective term with the displayed splitting, define

$$
\rho_{F^r}:=
(Rh_*E\otimes p_r)\,\rho_r\,
Rh_*(1_E\otimes h^*i_r).
$$

The bounded totalization of the $\rho_{F^r}$ is denoted
$\rho_{h,E,F}$.
