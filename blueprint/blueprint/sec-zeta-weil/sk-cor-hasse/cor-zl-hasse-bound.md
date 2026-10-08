+++
id = "cor-zl-hasse-bound"
kind = "theorem"
title = "Hasse–Weil bound"
order = 2915
tags = ["latex:corollary"]
uses = ["cor-trf-point-counting", "def-sc-curves", "def-sc-genus", "def-weil-algebraically-closed-coefficients", "def-weil-derived-complete-integral-detailed", "def-weil-finite-field-fiber", "def-weil-frobenius-coefficient-twists", "def-weil-geometric-hypotheses", "def-weil-rationalization-karoubi", "prop-cohomological-finiteness", "prop-endpoints", "prop-weight-purity-roots", "thm-sc-proper-cohomology"]
+++
Fix the finite-field datum
$(p,a,q,k_0,k)$, where $q=p^a$, choose a prime $\ell\neq p$, fix an
isomorphism $\iota:\Qlb\xrightarrow{\sim}\mathbf C$, and let
$C_0/k_0$ be a smooth, proper,
geometrically connected scheme of pure dimension $1$. Put
$C=C_0\times_{k_0}k$, and let

$$
g=g(C)=\dim_kH^1(C,\mathcal O_C)
$$

be the genus of the
smooth proper connected curve $C$ over the
algebraically closed field $k$. Then, for every integer $n\geq1$,

$$
\boxed{
\left|\#C_0(\mathbf F_{q^n})-(q^n+1)\right|\leq2g\,q^{n/2}}.
$$

## Proof

Step 1: the point-count identity. The scheme $C_0$ is proper, so by
[cor-trf-point-counting] applied to the constant Weil sheaf,

$$
N_n:=\#C_0(\mathbf F_{q^n})
=\sum_{i\in\mathbf Z}(-1)^i\Tr\bigl(F^n\mid H^i(C,\Qlb)\bigr),
$$

where $F$ is the global geometric Frobenius in the
geometric-Frobenius convention.

Step 2: the range and the degree zero. By
[prop-cohomological-finiteness] (the constant sheaf on a scheme of
dimension $1$), $H^i(C,\Qlb)=0$ for $i\notin[0,2]$, and
$H^0(C,\Qlb)\cong\Qlb$ with geometric Frobenius acting as the
identity; hence $\Tr(F^n\mid H^0(C,\Qlb))=1$ for every $n$.

Step 3: the top degree. By [prop-endpoints] with $d=1$,
$H^2(C,\Qlb)\cong\Qlb(-1)$ Frobenius-equivariantly, and by
[def-weil-frobenius-coefficient-twists] geometric Frobenius acts on
$\Qlb(-1)$ by $q$; hence $\Tr(F^n\mid H^2(C,\Qlb))=q^n$.

Step 4: the dimension of $H^1$. By
[thm-sc-proper-cohomology] (the Kummer computation for a smooth
proper curve of genus $g$ over the algebraically closed field $k$),
for every $n'=\ell^r$, $r\geq1$, prime to $\operatorname{char}k$,

$$
H^1(C,\mathbf F_{n'})\cong(\mathbf Z/n'\mathbf Z)^{2g},
$$

and $H^q(C,\mathbf F_{n'})=0$ for $q>2$. The coefficient
construction of the framework chapter is levelwise: the derived-complete
integral coefficients of [def-weil-derived-complete-integral-detailed], the
rationalization of [def-weil-rationalization-karoubi], and the
common-stage extension of
[def-weil-algebraically-closed-coefficients] assemble these finite
levels, so

$$
\dim_{\Qlb}H^1(C,\Qlb)=2g.
$$

Step 5: the trace bound. By [prop-weight-purity-roots] with
$i=1$ and $d=1$, every eigenvalue $\alpha$ of $F$ on
$H^1(C,\Qlb)$ satisfies $|\iota(\alpha)|=q^{1/2}$. Let
$\alpha_1,\ldots,\alpha_{2g}$ be the eigenvalues with algebraic
multiplicity (Step 4). The trace equals the sum of the eigenvalues,
so, applying the field isomorphism $\iota$ and the triangle inequality
in $\mathbf C$,

$$
\left|\iota\bigl(\Tr(F^n\mid H^1(C,\Qlb))\bigr)\right|
\leq\sum_{j=1}^{2g}|\iota(\alpha_j)|^n=2g\,q^{n/2}.
$$

Step 6: assembly. Combining Steps 1, 2 and 3,

$$
N_n-1-q^n=-\Tr\bigl(F^n\mid H^1(C,\Qlb)\bigr)
\quad\text{in }\Qlb.
$$

The left-hand side is an integer, hence fixed by $\iota$, so by
Step 5,

$$
|N_n-(q^n+1)|=\left|\iota\bigl(\Tr(F^n\mid H^1(C,\Qlb))\bigr)\right|
\leq2g\,q^{n/2},
$$

which is the claimed bound.
