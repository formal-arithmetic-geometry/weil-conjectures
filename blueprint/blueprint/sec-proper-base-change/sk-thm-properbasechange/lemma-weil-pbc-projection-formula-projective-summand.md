+++
id = "lemma-weil-pbc-projection-formula-projective-summand"
kind = "lemma"
title = "Finite-projective summand equations"
order = 1266
uses = ["def-weil-pbc-projection-formula-arrows", "lemma-weil-pbc-projection-formula-finite-free"]
+++
For a finite projective $F^r$ and a displayed splitting $(i_r,p_r)$, the
arrows $\pi_{h,E,F^r}$ and $\rho_{F^r}$ are inverse and are independent of
the chosen finite-free summand presentation.

## Proof

Let $A(u)=Rh_*E\otimes u$ and
$B(u)=Rh_*(E\otimes h^*u)$. Naturality of the counit gives

$$
B(i_r)\pi_{F^r}=\pi_rA(i_r),\qquad
B(p_r)\pi_r=\pi_{F^r}A(p_r).
$$

Using $p_ri_r=1$ and the finite-free inverse equations, compute

$$
\rho_{F^r}\pi_{F^r}
=A(p_r)\rho_rB(i_r)\pi_{F^r}
=A(p_r)\rho_r\pi_rA(i_r)=1,
$$

and

$$
\pi_{F^r}\rho_{F^r}
=\pi_{F^r}A(p_r)\rho_rB(i_r)
=B(p_r)\pi_r\rho_rB(i_r)=1.
$$

Thus $\rho_{F^r}$ is the unique inverse of the intrinsic map $\pi_{F^r}$;
uniqueness removes the dependence on $(i_r,p_r)$.
