+++
id = "def-weil-pbc-eight-curve-assertions"
kind = "definition"
title = "The eight curve-cohomology assertions"
order = 1106
uses = ["def-weil-pbc-C1", "def-weil-pbc-C2", "def-weil-pbc-C3", "def-weil-pbc-C4", "def-weil-pbc-C5", "def-weil-pbc-C6", "def-weil-pbc-C7", "def-weil-pbc-C8", "def-weil-pbc-curve-setting"]
+++
Let $k$ be algebraically closed, let $X$ be separated of finite type over
$k$ with $\dim X\leq1$, and let $F$ be a torsion sheaf on $X_{\mathrm{et}}$.
Write $\mathcal C_r(X,F)$, $1\leq r\leq8$, for the following assertions:

1. $H^q(X,F)=0$ for $q>2$;
1. $H^q(X,F)=0$ for $q>1$ when $X$ is affine;
1. $H^q(X,F)=0$ for $q>1$ when $\operatorname{char}k=p>0$ and $F$ is
$p$-power torsion;
1. every $H^q(X,F)$ is finite when $F$ is constructible and its torsion
is prime to $\operatorname{char}k$;
1. every $H^q(X,F)$ is finite when $X$ is proper and $F$ is
constructible;
1. for every algebraically closed extension $k'/k$, the restriction
$H^q(X,F)\to H^q(X_{k'},F|_{X_{k'}})$ is an isomorphism when the torsion
of $F$ is prime to $\operatorname{char}k$;
1. the map in (6) is an isomorphism when $X$ is proper, without a
restriction on the torsion;
1. for every open $a:W\hookrightarrow X$, the restriction
$H^2(X,F)\to H^2(W,a^{-1}F)$ is surjective.

## Detailed form

For a curve coefficient pair [def-weil-pbc-curve-setting] $(C,F)$, write
$\mathcal C(C,F)$ for the conjunction of the eight assertions

$$
 \mathcal C(C,F)=\bigwedge_{j=1}^{8}\mathcal C_j(C,F),
$$

namely [def-weil-pbc-C1], [def-weil-pbc-C2], [def-weil-pbc-C3],
[def-weil-pbc-C4], [def-weil-pbc-C5], [def-weil-pbc-C6], [def-weil-pbc-C7]
and [def-weil-pbc-C8].
