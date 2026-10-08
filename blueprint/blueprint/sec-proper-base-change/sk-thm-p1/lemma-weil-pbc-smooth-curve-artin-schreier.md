+++
id = "lemma-weil-pbc-smooth-curve-artin-schreier"
kind = "lemma"
title = "Smooth characteristic-$p$ Artin–Schreier calculation"
order = 1147
uses = ["def-weil-pbc-eight-curve-assertions"]
+++
Let $k$ be algebraically closed of characteristic $p>0$ and let $C$ be a
smooth separated finite-type scheme of dimension at most one. All
applicable assertions $\mathcal C_r(C,\underline{\mathbf F_p})$ hold.
For proper $C$, invariance under algebraically closed extension is induced
by the kernel of Frobenius minus the identity on $H^1(C,\mathcal O_C)$.

## Proof

The Artin–Schreier sequence on the etale site is

$$
0\longrightarrow\underline{\mathbf F_p}\longrightarrow\mathcal O_C
\xrightarrow{F-1}\mathcal O_C\longrightarrow0.
$$

Exactness on the right is checked on an etale neighbourhood by adjoining a
root of $T^p-T-a$; its derivative is $-1$, so that neighbourhood is etale.
Etale cohomology of the quasi-coherent sheaf $\mathcal O_C$ equals its
Zariski cohomology.

If $C$ is affine, $H^q(C,\mathcal O_C)=0$ for $q>0$. The long exact
sequence gives

$$
H^1(C,\mathbf F_p)=
\operatorname{coker}\bigl(F-1:\Gamma(C,\mathcal O_C)\to
\Gamma(C,\mathcal O_C)\bigr),\qquad
H^q(C,\mathbf F_p)=0\quad(q>1).
$$

This proves assertions (1)–(3) and (8) in the affine case; no
field-extension assertion for affine $p$-torsion is claimed.

Suppose $C$ is proper and connected. Then
$H^0(C,\mathcal O_C)=k$, $H^q(C,\mathcal O_C)=0$ for $q>1$, and
$E=H^1(C,\mathcal O_C)$ has dimension $g$. Since $a\mapsto a^p-a$ is
surjective on the algebraically closed field $k$, the long exact sequence
reduces to

$$
H^1(C,\mathbf F_p)=\ker(F-1:E\to E),\qquad
H^2(C,\mathbf F_p)=\operatorname{coker}(F-1:E\to E).
$$

Choose a basis of $E$. The additive map $F-1$ is a morphism
$\mathbf A_k^g\to\mathbf A_k^g$ whose derivative is $-\operatorname{id}$.
Its kernel is therefore zero-dimensional etale and finite. The image is an
open subgroup of the connected additive group $\mathbf A_k^g$, hence is the
whole group. Thus the cokernel is zero and the kernel is a finite
$\mathbf F_p$-vector space.

Proper coherent base change identifies
$E\otimes_kk'$ with $H^1(C_{k'},\mathcal O_{C_{k'}})$ and carries Frobenius
to Frobenius. The finite etale kernel of $F-1$ is a finite disjoint union
of copies of $\operatorname{Spec}k$; after an algebraically closed extension
it has the same geometric points. Hence
$H^1(C,\mathbf F_p)\to H^1(C_{k'},\mathbf F_p)$ is an isomorphism, while
degree zero is $\mathbf F_p$ and all degrees above one vanish. This proves
(1), (3), (5), (7), and (8) in the proper case, with the exact comparison
map specified by the Artin–Schreier sequence.
