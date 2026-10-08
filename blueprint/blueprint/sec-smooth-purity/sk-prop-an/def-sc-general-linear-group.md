+++
id = "def-sc-general-linear-group"
kind = "definition"
title = "The general and special linear group schemes"
order = 1966
uses = ["def-sc-gm-ga", "def-sc-group-scheme", "def-sc-group-scheme-subgroup"]
+++
Let $k$ be a field and $c\geq1$. The *general linear group
scheme* is the affine scheme

$$
\mathrm{GL}_{c,k}:=\Spec k[x_{ij}:1\leq i,j\leq c]\bigl[1/\det\bigr],
\qquad
\det:=\sum_{\sigma\in\mathfrak S_c}\operatorname{sgn}(\sigma)
\prod_{i=1}^{c}x_{i\sigma(i)},
$$

with comultiplication $m^*(x_{ij})=\sum_{r=1}^{c}x_{ir}\otimes x_{rj}$,
counit $\varepsilon(x_{ij})=\delta_{ij}$ and antipode
$i^*(x_{ij})=(-1)^{i+j}M_{ji}/\det$, where $M_{ji}$ is the
determinant of the matrix obtained from $(x_{kl})$ by deleting row
$j$ and column $i$; the group-scheme axioms of
[def-sc-group-scheme] hold because matrix multiplication is
associative, $1$ is a unit and $A\cdot A^{\mathrm{adj}}=\det(A)\cdot1$
with $A^{\mathrm{adj}}=(M_{kl})$. Its $R$-points are
$\mathrm{GL}_c(R)$, the group of invertible $c\times c$ matrices over
$R$. The *special linear group scheme* is the closed
subgroup scheme

$$
\mathrm{SL}_{c,k}:=\Spec k[x_{ij}]/(\det-1)\subseteq\mathrm{GL}_{c,k}.
$$

The determinant defines a homomorphism
$\det:\mathrm{GL}_{c,k}\to\mathbf G_m$ with
[def-sc-gm-ga], dual to $t\mapsto\det$; it is multiplicative
because $\det(AB)=\det(A)\det(B)$.
