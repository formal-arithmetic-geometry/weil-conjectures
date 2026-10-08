+++
id = "sbc-lem-bc-integral-base"
kind = "lemma"
title = "Integral base change on the source"
order = 1395
uses = ["lemma-weil-pbc-finite-direct-image-exact", "sbc-def-base-change-map", "sbc-def-base-change-property", "sbc-lem-integral-etale-direct-image-exact"]
+++
With $f:X\to S$ and $n$ as in [sbc-def-base-change-property] and some
$q\geq1$ (no base-change hypothesis on $f$ is needed here), consider
commutative
diagrams

$$
\begin{array}{ccccccc}
X & \xleftarrow{\;\;} & X' & \xleftarrow{\pi'} & X'' & &
Y\\
f\big\downarrow & & \big\downarrow f' & & \big\downarrow f'' & &
\big\downarrow e\\
S & \xleftarrow{\;\;} & S' & \xleftarrow{\;\pi\;} & S'' & &
T
\end{array}
$$

and the diagram with the outer
$h=h'\circ\pi''$, $g=g'\circ\pi$ (as horizontal composites), all squares
Cartesian, $g'$ quasi-compact and quasi-separated, and $\pi$ integral.
Let $\mathcal F$ be an abelian sheaf on $T_{\Et}$ annihilated by $n$.
If

$$
f'^{-1}R^qg_*\mathcal F\xrightarrow{\ \sim\ }R^qh_*e^{-1}\mathcal F
$$

is an isomorphism, then
$f''^{-1}R^qg'_*\mathcal F\to R^qh'_*e^{-1}\mathcal F$ is an
isomorphism.
(*Stacks Project, Lemma 59.88.4, [Tag `0F05`](https://stacks.math.columbia.edu/tag/0F05).*)

## Proof

Since $\pi$ and $\pi'$ are integral, $\pi_*$ and $\pi'_*$ are exact
by [sbc-lem-integral-etale-direct-image-exact] (finite case
[lemma-weil-pbc-finite-direct-image-exact]) and
$(f')^{-1}\pi_*=\pi'_*(f'')^{-1}$, so
$\pi'_*(f'')^{-1}R^qg'_*\mathcal F=(f')^{-1}R^qg_*\mathcal F$ and
$\pi'_*R^qh'_*e^{-1}\mathcal F=R^qh_*e^{-1}\mathcal F$; hence the
assumption says that the map for $f''$ becomes an isomorphism after
$\pi'_*$. It remains to see that the exact functor $\pi'_*$ is conservative;
apply it to the kernel and cokernel $\mathcal C$ of that map, so
$\pi'_*\mathcal C=0$. Let $\bar x''$ be a geometric point of $X''$ and
$\bar x'$ its image. The stalk $(\pi'_*\mathcal C)_{\bar x'}$ is
$\Gamma(\operatorname{Spec}B,\mathcal C)$ with
$B$ the ring of
$X''\times_{X'}\operatorname{Spec}\mathcal O^{\mathrm{sh}}_{X',\bar x'}$ over an
affine neighbourhood, an integral algebra over the strictly henselian ring
$A=\mathcal O^{\mathrm{sh}}_{X',\bar x'}$. Write $B=\operatorname{colim}B_\lambda$
with $B_\lambda$ finite over $A$; each $B_\lambda$ is a finite product of
strictly henselian local rings, so sections over $\operatorname{Spec}B_\lambda$
are the product of the stalks at their closed points, and the stalk
$\mathcal C_{\bar x''}$ is the colimit of the factors through which
$\bar x''$ passes. Hence $\mathcal C_{\bar x''}$ is a quotient of
$(\pi'_*\mathcal C)_{\bar x'}=0$, so $\mathcal C=0$. No surjectivity of
$\pi$ is needed, and the map for $f''$ is an isomorphism.
