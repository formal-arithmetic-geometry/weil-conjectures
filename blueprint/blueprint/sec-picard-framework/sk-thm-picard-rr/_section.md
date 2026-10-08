+++
id = "sk-thm-picard-rr"
kind = "section"
title = "Riemann–Roch for curves, and its geometric corollary"
order = 705
uses = ["sk-def-av-jacobian", "sk-def-av-pic", "sk-thm-picard-duality"]
lean = ["AlgebraicGeometry.Scheme.eulerChar_free_eq", "AlgebraicGeometry.Scheme.eulerChar_unit_eq", "AlgebraicGeometry.Scheme.finrankH_zero_eq", "AlgebraicGeometry.Scheme.isAmple_of_degree_pos", "AlgebraicGeometry.Scheme.isAffine_compl_of_isAmple"]
+++
*Theorem (sketch).*

Let $X$ be a smooth proper curve over $k$ with $H^0(X,\cO_X)=k$ (e.g.
the base change to any field of a smooth projective curve over an
algebraically closed field), of genus $g=\dim_kH^1(X,\cO_X)$ (as in the
conventions; flat base change preserves $h^0$ and $h^1$), and $\cF$
coherent, with $\chi(\cF)=\sum_q(-1)^q\dim_kH^q(X,\cF)$.

*Degrees.* For a divisor $D=\sum_xn_x\,x$ ($x$ closed points)
put $\deg D=\sum_xn_x[\kappa(x):k]$. Principal divisors have degree
$0$ (for $f\in k(X)\setminus k$, $\operatorname{div}f=f^*(0)-f^*(\infty)$
for the finite flat $f:X\to\mathbf P^1_k$, both of degree $[k(X):k(f)]$),
and every line bundle is $\cL\cong\cO_X(D)$ (divisor of a nonzero
rational section), so $\deg\cL:=\deg D$ is well defined and additive.
For coherent $\cF$ with torsion subsheaf $\mathcal T$ and locally free quotient
$\mathcal E=\cF/\mathcal T$ of rank $\rk\cF$, put
$\deg\cF:=\sum_x\operatorname{length}_{\cO_{X,x}}(\cT_x)[\kappa(x):k]+\deg(\det\mathcal E)$
$=\dim_kH^0(X,\mathcal T)+\deg(\det\mathcal E)$.

1. ****(RR)**** $\chi(\cF)=\deg\cF+\rk(\cF)(1-g)$; in
particular $\chi(\cO_X)=1-g$, and for every line bundle
$\deg\cL=\chi(\cL)-\chi(\cO_X)$, i.e. the divisor degree agrees with
the $\chi$-degree used for the Picard scheme below (so the two
definitions of $\Pic^0$, as kernel of either degree, coincide); and
for a line bundle of degree $d$ with $d\ge2g-1$: $h^0(\cL)=d+1-g$.
1. ****(G)**** *positive degree $\Rightarrow$ ample:* if
$\cL$ is a line bundle on $X$ with $\deg\cL>0$, then $\cL$ is ample
($h^0(\cL^{\otimes m})=m\deg\cL+1-g$ grows, and after base change to
$\bar k$, where all closed points are rational, base-point freeness and
the separation of points and tangent vectors follow from (RR) by
subtracting one or two points; over a general $k$ subtracting a closed
point $P$ changes $h^0$ by $[\kappa(P):k]$, not by $1$).
1. ****(H)**** *affine complement:* if $\cL$ is ample
and $D$ an effective Cartier divisor with $\cL\cong\cO_X(D)$, then
$X\setminus\operatorname{Supp}(D)$ is affine.

## Proof

(RR): by additivity of $\chi$ in short exact sequences, the torsion
part of $\cF$ (for which $\chi=h^0$ is the length, i.e. the degree) and a
filtration of the locally free quotient by line bundles (along which
$\deg\det$ is additive) reduce the formula to
line bundles $\cO_X(D)$. There $0\to\cO_X(D-x)\to\cO_X(D)\to\kappa(x)\to0$
gives $\chi(\cO_X(D))=\chi(\cO_X(D-x))+[\kappa(x):k]$ (coherent
cohomology vanishes in degrees $\ge2$ on the one-dimensional noetherian
space $X$, so $\chi=h^0-h^1$ throughout); applied to $D$ when $n_x>0$
and to $D+x$ when $n_x<0$ (where it reads
$\chi(\cO_X(D))=\chi(\cO_X(D+x))-[\kappa(x):k]$), it lowers
$\sum_x|n_x|$ by one and leaves $\chi-\deg$ unchanged, so by induction on
$\sum_x|n_x|$, $\chi(\cO_X(D))=\deg D+\chi(\cO_X)$, and
$\chi(\cO_X)=h^0-h^1=1-g$ by the hypotheses; this is also the equality
$\deg\cL=\chi(\cL)-\chi(\cO_X)$. For $d\ge2g-1$,
[sk-thm-picard-duality] gives
$H^1(\cL)^\vee\cong H^0(\omega_X\otimes\cL^{-1})=0$, the latter of
negative degree ($\deg\omega_X=\chi(\omega_X)-\chi(\cO_X)=2g-2$, as
duality gives $h^0(\omega_X)=g$, $h^1(\omega_X)=1$; a nonzero section
would give an effective divisor of negative degree), whence $h^0(\cL)=d+1-g$. (G): ampleness descends along the
fpqc cover $\Spec\bar k\to\Spec k$ and $\deg$ is preserved by flat
base change, and $X_{\bar k}$ is again a smooth proper connected curve
of genus $g$ with $H^0=\bar k$ ($X$ is geometrically reduced with
$H^0(X,\cO_X)=k$, hence geometrically integral); so we may take $k$
algebraically closed, where every closed point is rational. Then for
$m\deg\cL\ge2g+1$ and closed points $P,Q$ (possibly equal), (RR) in
the range $d\ge2g-1$ gives
$h^0(\cL^{\otimes m}(-P))=h^0(\cL^{\otimes m})-1$ and
$h^0(\cL^{\otimes m}(-P-Q))=h^0(\cL^{\otimes m})-2$, i.e.
$\cL^{\otimes m}$ is base-point free and separates points and tangent
vectors; hence $\cL^{\otimes m}$ is very ample and $\cL$ is ample.
(H): classical (the complement of an
ample effective divisor is affine).
