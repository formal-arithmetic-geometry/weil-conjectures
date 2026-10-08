+++
id = "lemma-constructible-hom-constant-locally"
kind = "lemma"
title = "Morphisms between constant sheaves"
order = 1296
lean = ["CategoryTheory.Sheaf.isConstant_cokernel_over", "CategoryTheory.Sheaf.isConstant_kernel_over", "CategoryTheory.exists_mem_forall_exists_constantSheafOverHom_comp_map_eq", "CategoryTheory.exists_mem_forall_exists_linearMap"]
uses = ["def-constructible-constant"]
+++
Let $\mathcal A=\mathrm{Mod}_\Lambda$ with $\Lambda$ a ring, let $M$ be a finite
$\Lambda$-module, let $N$ be a $\Lambda$-module and let $\varphi\colon M_X\to N_X$ be a
morphism of constant sheaves on $\et X$. Then there is an étale cover
$(U_i\to X)_i$ such that $\varphi|_{U_i}$ is induced by a $\Lambda$-linear
map $f_i\colon M\to N$, i.e. equals $(f_i)_{U_i}\colon M_{U_i}\to N_{U_i}$.
Consequently the kernel and the cokernel of $\varphi$ are locally constant,
with restrictions $(\ker f_i)_{U_i}$ and $(\operatorname{coker}f_i)_{U_i}$.

## Proof

By the adjunction between constant sheaves and global sections,
$\Hom(M_X,N_X)=\Hom_\Lambda(M,\Gamma(X,N_X))$. A global section of $N_X$
over $X$ is, on an étale cover, a section of the constant presheaf, that
is, an element of $N$; hence, on an étale cover $(U_i\to X)_i$ obtained by
intersecting the covering sieves for the finitely many sections $\varphi(m)$,
$m\in M$, every $\varphi(m)$ is the constant section $n_{i,m}$ over $U_i$.
Over a nonempty $U_i$ the map $N\to\Gamma(U_i,N_X)$ is injective (a
section of the constant presheaf which becomes zero in the sheafification
vanishes on a covering sieve, whose members are nonempty), so
$m\mapsto n_{i,m}$ is $\Lambda$-linear, giving $f_i\colon M\to N$ with
$\varphi|_{U_i}$ the morphism of constant sheaves induced by $f_i$ (both
morphisms out of the constant sheaf $M_{U_i}$ have the same adjoint
$M\to\Gamma(U_i,N_X)$; here one uses that the restriction of a constant
sheaf to $\et{U_i}$ is the constant sheaf, compatibly with the unit maps).
Empty $U_i$ are discarded from the cover.
Since restriction to $\et{U_i}$ is exact and the constant sheaf functor is
exact (a composite of the exact constant presheaf functor and
sheafification), the kernel and cokernel of $\varphi|_{U_i}$ are the
constant sheaves on $\ker f_i$ and $\operatorname{coker}f_i$.
