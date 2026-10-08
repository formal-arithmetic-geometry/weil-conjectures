+++
id = "lem-tate-module-no-fixed"
kind = "lemma"
title = "No fixed vectors on the Tate module when the fixed subgroup is finite"
order = 2563
uses = ["def-tate-module-abelian-group"]
lean = ["AddCommGroup.eq_zero_of_mem_tateModule_of_forall_fixed"]
+++
Let $M$ be an abelian group, $\ell$ a prime, and $\sigma$ an automorphism of $M$
whose fixed subgroup $M^\sigma$ is finite. Then $T_\ell M$ has no $\ell$-power
torsion, $(T_\ell M)^\sigma=0$, and $(V_\ell M)^\sigma=0$ (in the notation of
[def-tate-module-abelian-group]); the same holds for $\sigma^{-1}$.

## Proof

$T_\ell M$ has no $\ell$-torsion:
$\ell t=0$ implies $t_n=\ell t_{n+1}=0$; iteration excludes all
$\ell$-power torsion. Thus its map into the localization is injective.
If $\ell^{-b}t$ is fixed, this injectivity gives $\sigma t=t$.
All $t_n$ lie in the finite group $M^\sigma$, whose $\ell$-primary
subgroup is killed by a uniform $\ell^e$. Compatibility then gives
$t_n=\ell^et_{n+e}=0$. Finally an automorphism and its inverse have the
same fixed vectors, so the assertion holds for $\sigma^{-1}$.
