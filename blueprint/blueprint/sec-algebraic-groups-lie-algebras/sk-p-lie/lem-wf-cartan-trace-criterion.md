+++
id = "lem-wf-cartan-trace-criterion"
kind = "lemma"
title = "Cartan's trace criterion"
order = 2470
uses = ["lem-wf-engel-matrix"]
+++
Let $M$ be a finite-dimensional vector space over $\Qlb$, and let
$\mathfrak a\subseteq\operatorname{End}(M)$ be a
finite-dimensional Lie algebra. If

$$
\operatorname{tr}(XY)=0
\quad\text{for all }X\in[\mathfrak a,\mathfrak a]
\text{ and }Y\in\mathfrak a,
$$

then $\mathfrak a$ is solvable.

## Proof

Let $\mathfrak d=[\mathfrak a,\mathfrak a]$. We first show that
every $X\in\mathfrak d$ is nilpotent. Write the ordinary Jordan
decomposition of the matrix $X$ as $X=S+N$, where $S$ is
diagonalizable, $N$ is nilpotent, and $SN=NS$. In a basis which
diagonalizes $S$, the operator
$\operatorname{ad}X:Y\mapsto XY-YX$ on $\operatorname{End}(M)$
has Jordan decomposition
$\operatorname{ad}S+\operatorname{ad}N$: the first summand is
diagonalizable, the second nilpotent, and they commute. For each
eigenvalue $\delta$ of $\operatorname{ad}X$, let $e_\delta$ be
the size of its largest Jordan block. Hermite interpolation gives a
polynomial $P$ such that

$$
P(t)\equiv0\pmod{t^{e_0}},\qquad
P(t)\equiv\delta\pmod{(t-\delta)^{e_\delta}}
\quad(\delta\ne0).
$$

Here $e_0$ is the size of the largest Jordan block for the zero
eigenvalue. On the generalized zero-eigenspace this polynomial kills
the whole nilpotent block, while on a generalized
$\delta$-eigenspace with $\delta\ne0$ it retains the scalar
$\delta$ and kills its nilpotent part; hence
$\operatorname{ad}S=P(\operatorname{ad}X)$. Since $\mathfrak d$ is
an ideal of $\mathfrak a$, $\operatorname{ad}X$ carries
$\mathfrak a$ into $\mathfrak d$, and hence
$[S,\mathfrak a]\subseteq\mathfrak d$. The same calculation with
commutators shows that $\operatorname{ad}S$ preserves $\mathfrak d$.

Let $\lambda_1,\ldots,\lambda_N$ be the eigenvalues of $S$, with
algebraic multiplicity, and let $E$ be their finite-dimensional
$\mathbf Q$-linear span. For a $\mathbf Q$-linear map
$f:E\to\Qlb$, define $Z_f$ to act by $f(\lambda)$ on the
$\lambda$-eigenspace of $S$. Choose a polynomial $R_f$ satisfying

$$
R_f(\lambda_i-\lambda_j)=f(\lambda_i-\lambda_j)
\quad\text{for all }i,j,\qquad R_f(0)=0.
$$

This is ordinary interpolation on the finite set of differences (the
value at $0$ is already $f(0)=0$). On
$\operatorname{Hom}(M_{\lambda_i},M_{\lambda_j})$, both sides have
the same scalar action, so
$\operatorname{ad}Z_f=R_f(\operatorname{ad}S)$. Thus
$[Z_f,\mathfrak a]\subseteq\mathfrak d$.

Write $X=\sum_j[A_j,B_j]$. Cyclicity of trace and the preceding
containment give

$$
\operatorname{tr}(XZ_f)
=\sum_j\operatorname{tr}([Z_f,A_j]B_j)=0.
$$

Because $N$ preserves every $S$-eigenspace and is nilpotent there,
$\operatorname{tr}(NZ_f)=0$; hence

$$
\sum_{i=1}^N f(\lambda_i)\lambda_i
=\operatorname{tr}(SZ_f)=0. \tag{*}
$$

Choose a $\mathbf Q$-basis $e_1,\ldots,e_d$ of $E$, write
$\lambda_i=\sum_j a_{ij}e_j$ with $a_{ij}\in\mathbf Q$, and put
$f_j(e_k)=\delta_{jk}$. Comparing the coefficient of $e_j$ in
$(*)$ for $f=f_j$ gives $\sum_i a_{ij}^2=0$. A sum of squares
of rational numbers is zero only when every summand is zero. Thus all
$\lambda_i$ vanish and $X$ is nilpotent. Hence every element of
$\mathfrak d$ is nilpotent; by [lem-wf-engel-matrix],
$\mathfrak d$ is nilpotent and hence solvable. The quotient
$\mathfrak a/\mathfrak d$ is abelian. Appending the derived series
of $\mathfrak d$ to the first step
$\mathfrak a\supseteq\mathfrak d$ therefore gives a terminating
derived series for $\mathfrak a$, so $\mathfrak a$ is solvable.
