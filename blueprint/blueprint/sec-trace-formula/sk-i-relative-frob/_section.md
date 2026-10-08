+++
id = "sk-i-relative-frob"
kind = "section"
title = "Relative Frobenius"
order = 2361
uses = ["sk-d-relative-frob", "sk-d-setup"]
lean = ["AlgebraicGeometry.ProEtale.isFinite_relativeFrobenius_and_isUniversalHomeomorphism"]
+++
*Proposition (sketch).*

The map $r_m$ of the factorization is a finite
universal homeomorphism.

## Proof

Put $Q=q^m$. By [sk-d-relative-frob], $r_m=(f,\Phi_{X,m})$ is the base
change along $\mathbf F_q\to k$ of the relative $Q$-power Frobenius
$F_{X_0/Y_0}:X_0\to X_0^{(Q)}=Y_0\times_{F_{Y_0},Y_0,f_0}X_0$, and
$\pi\circ F_{X_0/Y_0}=F_{X_0}$ for the projection $\pi:X_0^{(Q)}\to X_0$,
the base change of the absolute $Q$-power Frobenius $F_{Y_0}$ along $f_0$.
Finite morphisms and universal homeomorphisms are stable under base change,
so it suffices to treat $F_{X_0/Y_0}$.

*Finiteness.* Affine-locally $F_{X_0/Y_0}$ is
$R\otimes_{F,R}S\to S$, $r\otimes s\mapsto f_0^\#(r)s^{Q}$. Its image
contains $f_0^\#(R)$ and all $Q$-th powers, so if $s_1,\dots,s_n$ generate
$S$ over $R$, the $Q^n$ monomials $\prod_is_i^{b_i}$ with $0\le b_i<Q$
generate $S$ as a module over the image. Hence $F_{X_0/Y_0}$ is finite, in
particular integral.

*Universal homeomorphism.* This is *not* tested on $T$-valued points for
arbitrary test rings $T$: a universal homeomorphism need not induce
bijections on $T$-points, and $p$-th roots need neither exist ($t$ in
$\mathbf F_q[t]$) nor be unique ($0$ and $\epsilon$ in
$\mathbf F_q[\epsilon]/(\epsilon^p)$). Use instead the characterization
[Stacks, Tag 04DF](https://stacks.math.columbia.edu/tag/04DF): a morphism
is a universal homeomorphism if and only if it is integral, universally
injective and surjective, and universal injectivity is tested on points
with values in fields. The absolute Frobenius $F_T$ of any
$\mathbf F_p$-scheme is the identity on the underlying space and induces
the purely inseparable maps $a\mapsto a^{Q}$ on residue fields, so it is
integral, surjective and universally injective, hence a universal
homeomorphism; so are $F_{X_0}$, $F_{Y_0}$ and the base change $\pi$. Then
$F_{X_0/Y_0}$ is surjective because $\pi\circ F_{X_0/Y_0}=F_{X_0}$ is
surjective and $\pi$ is injective, and it is injective on $L$-valued points
for every field $L$ because $F_{X_0}$ is. Being integral, universally
injective and surjective, $F_{X_0/Y_0}$ is a universal homeomorphism
([Stacks, Tag 04DF](https://stacks.math.columbia.edu/tag/04DF); for $m=1$
this is the relative-Frobenius statement
[Stacks, Tag 0CCB](https://stacks.math.columbia.edu/tag/0CCB)). Base
changing to $k$ gives the claim for $r_m$.

Uses: [sk-d-relative-frob], [sk-d-setup]
