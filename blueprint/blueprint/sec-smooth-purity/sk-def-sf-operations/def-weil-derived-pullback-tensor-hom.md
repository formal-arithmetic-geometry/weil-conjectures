+++
id = "def-weil-derived-pullback-tensor-hom"
kind = "definition"
title = "Derived pullback, tensor product, and internal Hom"
order = 1467
uses = ["def-weil-algebraically-closed-coefficients", "def-weil-derived-complete-integral-detailed", "def-weil-derived-tensor", "def-weil-finite-torsion-constructibility", "def-weil-pbc-proetale-site", "def-weil-rationalization-karoubi", "def-weil-scheme-morphism-properties"]
+++
Fix a prime $\ell$, a finite extension $E/\Ql$, an integer $n\in\mathbf
Z_{\geq1}$, and put $A=A_{E,n}$. Let $X,Y$ be schemes on which $\ell$ is
invertible, let $f:X\to Y$ be a morphism
[def-weil-scheme-morphism-properties], and, for every coefficient level, let
$f_n$ denote the morphism $f$ equipped with coefficients in $A_{E,n}$. Use
the small pro-etale sites [def-weil-pbc-proetale-site] on $X$ and
$Y$. The symbol $A$ denotes the constant coefficient sheaf on each such site,
and $D(-,A)$ is its ambient derived category. For $K\in
D(Y_{\mathrm{proet}},A)$, and for every scheme $W\in\{X,Y\}$ and $M,N\in
D(W_{\mathrm{proet}},A)$, define

$$
 Lf^*K=f^{-1}K\otimes^L_{f^{-1}A}A,
 \qquad
 M\otimes_A^L N,
 \qquad
 R\mathcal Hom_A(M,N)
$$

using K-flat resolutions for the derived tensor products
[def-weil-derived-tensor] and a K-injective resolution of the second variable
for derived internal Hom. Finite-torsion coefficients use finite-torsion
constructibility [def-weil-finite-torsion-constructibility]. For integral
coefficients, the K-flat and K-injective resolutions are taken in the ambient
derived category of modules over the completed coefficient sheaf. The
derived-complete integral category
[def-weil-derived-complete-integral-detailed] is the specified full
subcategory; a resolution is not required to remain in that subcategory term
by term. Write

$$
 Lf_n^*=L(f_n)^*.
$$

For $\Lambda\in\{\mathcal O_E,E,\Qlb\}$, define the operation by the
compatible finite reductions, the derived inverse limit for $\mathcal O_E$,
the rationalization for $E$, and the common-stage coefficient construction
for $\Qlb$, using the rationalized coefficient category
[def-weil-rationalization-karoubi] and the algebraically closed coefficient
category [def-weil-algebraically-closed-coefficients].
