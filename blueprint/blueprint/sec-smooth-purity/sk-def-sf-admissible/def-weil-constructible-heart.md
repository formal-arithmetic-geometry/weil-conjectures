+++
id = "def-weil-constructible-heart"
kind = "definition"
title = "Constructible heart"
order = 1506
uses = ["def-weil-algebraically-closed-coefficients", "def-weil-finite-field-fiber", "def-weil-finite-torsion-constructibility", "def-weil-rationalization-karoubi", "def-weil-scheme-morphism-properties"]
+++
Fix the finite-field datum [def-weil-finite-field-fiber] $p,a,q,k_0,k$, a
prime $\ell\neq p$, write $\Ql=\mathbf Q_\ell$, choose an algebraic closure
$\Qlb$ of $\Ql$, and choose a finite-type
[def-weil-scheme-morphism-properties] $k$-scheme $Y$ and a finite extension
$E/\Ql$ contained in $\Qlb$. Let $\Lambda\in\{E,\Qlb\}$. For $\Lambda=E$, use
the rationalized coefficient category
[def-weil-rationalization-karoubi]; its integral representatives have
finite-level reductions satisfying the finite-torsion constructibility
condition [def-weil-finite-torsion-constructibility]. For $\Lambda=\Qlb$, use
the common-stage category
[def-weil-algebraically-closed-coefficients]. For every $m\in\mathbf Z$,
write $\tau^{\leq m}$ and $\tau^{\geq m}$ for the constructible truncation
functors obtained from the standard $t$-structure. For $\Lambda=E$ or
$\Qlb$, define

$$
\begin{aligned}
 D^{\leq0}_c(Y,\Lambda)&=
 \{K:\tau^{\geq1}K=0\},\\
 D^{\geq0}_c(Y,\Lambda)&=
 \{K:\tau^{\leq-1}K=0\}.
\end{aligned}
$$

Their intersection is the abelian category $\Sh_c(Y,\Lambda)$, called the
*constructible heart*; its objects are constructible $\Lambda$-adic sheaves
whose finite-level reductions satisfy the finite-torsion constructibility
condition [def-weil-finite-torsion-constructibility], with the rationalized
and common-stage interpretations supplied by the coefficient constructions.
