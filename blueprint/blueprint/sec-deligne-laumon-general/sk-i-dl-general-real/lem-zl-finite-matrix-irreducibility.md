+++
id = "lem-zl-finite-matrix-irreducibility"
kind = "lemma"
title = "Absolute irreducibility has a finite matrix witness"
order = 2831
uses = ["lem-wf-schur-scalar", "p-real-integral"]
+++
Let $E/\mathbf Q_\ell$ be finite, let $V$ be an $n$-dimensional
$E$-vector space, and let $\rho:\Pi\to\operatorname{GL}_E(V)$
be a continuous representation of a profinite group. Assume that
$V\otimes_E\Qlb$ is irreducible. There exist a stable
$\mathcal O_E$-lattice $L$ and $N\geq1$ such that any subgroup
$\Pi'\subset\Pi$ with the same image as $\Pi$ on
$L/\varpi_E^N L$ still acts absolutely irreducibly on $V$.

## Proof

First recall the elementary matrix-algebra argument behind Burnside's
lemma. If a unital algebra $A\subset\operatorname{End}_k(W)$ acts
irreducibly on a finite-dimensional vector space over an algebraically
closed field, Schur's lemma [lem-wf-schur-scalar] says
$\operatorname{End}_A(W)=k$. For linearly independent
$w_1,\ldots,w_r$, induction on $r$ shows that
$A\to W^r$, $a\mapsto(aw_1,\ldots,aw_r)$, is onto.
For the induction, its image projects onto $W^{r-1}$. The kernel
in the last copy of $W$ is an $A$-submodule, hence is either
$W$ or zero. In the latter case the image is the graph of an
$A$-linear map $W^{r-1}\to W$; Schur's lemma makes that map
$(v_i)\mapsto\sum c_i v_i$. Applying it to the tuple furnished by
$1\in A$ contradicts the independence of the $w_i$.
Taking a basis of $W$ proves $A=\operatorname{End}_k(W)$.

Apply this to the span of $\rho(\Pi)$ after extending scalars from
$E$ to $\Qlb$. The $E$-span already has dimension $n^2$,
so choose $g_1,\ldots,g_{n^2}\in\Pi$ whose matrices form an
$E$-basis of $\operatorname{End}_E(V)$.
Compactness of $\rho(\Pi)$ supplies a stable lattice (as in [p-real-integral]): for an initial
lattice $L_0$, all its translates lie in $\varpi_E^{-a}L_0$
for some $a$; their $\mathcal O_E$-span is a finitely generated
torsion-free module containing $L_0$, and hence is a lattice $L$.
It is stable under the whole group.

Write the matrices in a basis of $L$. The determinant $\Delta$
of their $n^2$ vectorized columns is a nonzero element of
$\mathcal O_E$. Choose $N>v_{\varpi_E}(\Delta)$.
If $\Pi'$ has the same finite reduction image, choose
$h_j\in\Pi'$ with
$\rho(h_j)\equiv\rho(g_j)\pmod{\varpi_E^N}$.
Their column determinant is congruent to $\Delta$ modulo
$\varpi_E^N$, so is nonzero. Thus the $E$-span of
$\rho(\Pi')$ is again the whole matrix algebra. The same is true
after extending scalars to $\Qlb$, which excludes any nonzero
proper invariant subspace. Continuity ensures that the reduction
image is a finite quotient of $\Pi$.
