+++
id = "sk-p-tate"
kind = "section"
title = "Tate modules and Frobenius"
order = 2562
uses = ["sk-d-ab-field", "sk-d-ab-tate"]
lean = ["AddCommGroup.eq_zero_of_mem_tateModule_of_forall_fixed"]
+++
*Proposition (sketch).*

For an abelian variety $A_0/k_0$, its
rational Tate module has no nonzero vector fixed by
geometric Frobenius:

$$
(V_\ell A)^F=0.
$$

## Proof

In the finite-field setting of [sk-d-ab-field], the fixed points of
$x\mapsto x^q$ in $\bar k$ are exactly $k_0$: the $q$ elements of $k_0$
exhaust the roots of $T^q-T$. On affine charts this gives
$A^\sigma=A_0(k_0)$, a finite group, since a point of a finitely generated
$k_0$-algebra is determined by finitely many values in $k_0$.
In [sk-d-ab-tate], $T_\ell M$ has no $\ell$-torsion:
$\ell t=0$ implies $t_n=\ell t_{n+1}=0$; iteration excludes all
$\ell$-power torsion. Thus its map into the localization is injective.
If $\ell^{-b}t$ is fixed, this injectivity gives $\sigma t=t$.
All $t_n$ lie in the finite group $A^\sigma$, whose $\ell$-primary
subgroup is killed by a uniform $\ell^e$. Compatibility then gives
$t_n=\ell^et_{n+e}=0$. Finally an automorphism and its inverse have the
same fixed vectors, so the assertion holds for $F$.

Uses: [sk-d-ab-field], [sk-d-ab-tate]
