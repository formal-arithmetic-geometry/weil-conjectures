+++
id = "thm-weil-final"
kind = "theorem"
title = "Weil conjectures for a smooth proper variety"
order = 2939
lean = ["AlgebraicGeometry.Scheme.weil_conjectures"]
uses = ["def-weil-point-counts-zeta", "def-weil-smooth-proper-cohomological-family", "prop-euler-product", "thm-weil-final-betti", "thm-weil-final-functional-equation", "thm-weil-final-integrality", "thm-weil-final-rationality", "thm-weil-final-rh"]
+++
Let $X_0$ be a smooth, proper, geometrically connected scheme of pure
dimension $d$ over $\Fq$. Put $X=X_0\times_{\Fq}k$, let
$\mathscr X$ be the resulting smooth-proper datum, and let
$P_i=P_i(\mathscr X)$ be the canonical factors of
Definition *Canonical integral cohomological factors*. Then the following
statements hold.

1. The zeta series has both point-counting descriptions
$$
Z(X_0,T)=
\exp\left(\sum_{n\geq1}
\#X_0(\mathbf F_{q^n})\frac{T^n}{n}\right)
=\prod_{x\in|X_0|}(1-T^{\deg(x)})^{-1},
$$
and belongs to $1+T\mathbf Z[[T]]\cap\mathbf Q(T)$.
1. The polynomials $P_i$ are the unique polynomials
$$
P_i(T)\in\mathbf Z[T]
\qquad(0\leq i\leq2d)
$$
with $P_i(0)=1$ such that, for every prime $\ell\neq p$,
$$
\bigl((\mathbf Z[T]\longrightarrow\Ql[T])(P_i)\bigr)(T)=
\det(1-TF\mid H^i(X,\Ql)).
$$
They give the rational factorization
$$
Z(X_0,T)=
\prod_{i=0}^{2d}P_i(T)^{(-1)^{i+1}}.
$$
1. Fix an algebraic closure $\overline{\mathbf Q}$ of $\mathbf Q$
and regard $P_i\in\mathbf Z[T]$ inside
$\overline{\mathbf Q}[T]$. For every $0\leq i\leq2d$, every
reciprocal root $\alpha\in\overline{\mathbf Q}$ of $P_i$ is an
algebraic integer
and a $q$-Weil number of weight $i$:
$$
|\tau(\alpha)|=q^{i/2}
$$
for every embedding
$\tau:\mathbf Q(\alpha)\hookrightarrow\mathbf C$. For every ordinary
root $\beta\in\overline{\mathbf Q}$ of $P_i$ and every embedding
$\tau:\mathbf Q(\beta)\hookrightarrow\mathbf C$, one has
$|\tau(\beta)|=q^{-i/2}$.
1. For every $0\leq i\leq2d$, with $b_i=\deg P_i$, and every
prime $\ell\neq p$,
$$
b_i=\dim_{\Ql}H^i(X,\Ql),
\qquad b_i=b_{2d-i},
\qquad b_0=b_{2d}=1,
$$
independently of $\ell$. Moreover
$$
P_0(T)=1-T,
\qquad
P_{2d}(T)=1-q^dT.
$$
In particular $Z(X_0,T)$ has a pole of order exactly $1$ at $T=1$
and, if $d\geq1$, a pole of order exactly $1$ at $T=q^{-d}$.
1. If
$$
D_i=(-1)^{b_i}[T^{b_i}]P_i(T),
\qquad
\chi=\sum_{i=0}^{2d}(-1)^ib_i,
$$
then $d\chi$ is even and, for every $0\leq i\leq2d$,
$$
P_{2d-i}(q^{-d}T^{-1})
=(-1)^{b_i}T^{-b_i}D_i^{-1}P_i(T),
$$
and
$$
Z(X_0,q^{-d}T^{-1})
=\varepsilon q^{d\chi/2}T^\chi Z(X_0,T)
$$
for the sign
$$
\varepsilon=
(-1)^\chi q^{-d\chi/2}
\prod_{i=0}^{2d}D_i^{(-1)^i}
\in\{1,-1\}.
$$

**Status.** Both Lean statements exist and both proofs are `sorry`.
`weil_conjectures` states clauses (ii), (iii) and
(v) for a smooth, proper, geometrically integral $X_0$, phrased
through the three predicates `IsWeilFactorization`,
`WeilFunctionalEquation` and `WeilRiemannHypothesis`, which are
complete definitions; `zetaSeries_rational` states the rationality
assertion of clause (i) for an arbitrary scheme of finite type over
$\Fq$.

## Proof

The hypotheses make $\mathscr X=(X_0,d,X)$ a smooth-proper datum, so all
degreewise factors and Frobenius operators in Definitions
`[def-weil-smooth-proper-cohomological-family]` and
*Frobenius characteristic factors* are available.

*Clause (i).*
Definition [def-weil-point-counts-zeta] is the exponential point-counting
description. Proposition [prop-euler-product] gives the closed-point
Euler product and membership in $1+T\mathbf Z[[T]]$. Proposition
`prop-integral-recovery` gives the factorization by integral
polynomials and hence $Z(X_0,T)\in\mathbf Q(T)$.
This proves exactly the two displayed descriptions and both coefficient
claims in (i).

*Clause (ii).*
Proposition `prop-integral-recovery` applies to the fixed datum and says
that the canonical $P_i\in\mathbf Z[T]$ have constant term one, satisfy

$$
\bigl((\mathbf Z[T]\longrightarrow\Ql[T])(P_i)\bigr)(T)=P_{i,\ell}(T)
=\det(1-TF\mid H^i(X,\Ql))
$$

for every prime $\ell\neq p$, are the unique integral family with those
realizations, and obey

$$
Z(X_0,T)=\prod_{i=0}^{2d}P_i(T)^{(-1)^{i+1}}
\quad\text{in }\mathbf Q(T).
$$

These are precisely all assertions of (ii).

*Clause (iii).*
Fix $0\leq i\leq2d$. Proposition
`prop-arithmetic-roots` applies to the polynomial $P_i$ in the fixed
algebraic closure. It states that every reciprocal root is an algebraic
integer and a $q$-Weil number of weight $i$, with the displayed equality
for every complex embedding. The same proposition identifies an ordinary
root $\beta$ with the inverse of a reciprocal root of this same
polynomial $P_i$, and gives $|\tau(\beta)|=q^{-i/2}$. This proves
(iii) without changing the root terminology.

*Clause (iv).*
Fix an integer $0\leq i\leq2d$. For every prime $\ell\neq p$,
Proposition `prop-integral-recovery` gives

$$
b_i=\deg P_i=\dim_{\Ql}H^i(X,\Ql),
$$

so the left-hand side is independent of $\ell$. Proposition
`prop-duality-reciprocity` gives $b_i=b_{2d-i}$, and Proposition
`prop-endpoints` gives

$$
b_0=b_{2d}=1,\qquad P_0(T)=1-T,\qquad P_{2d}(T)=1-q^dT.
$$

Theorem [thm-weil-final-betti] states all of these equalities for the
same datum and, in addition, that $Z(X_0,T)$ has a pole of order exactly
$1$ at $T=1$ and, when $d\geq1$, at $T=q^{-d}$. This is exactly (iv).

*Clause (v).*
The definitions of $D_i,\chi,\varepsilon$ are respectively
Definitions `def-weil-determinant-constants`,
*Euler characteristic*,
and `def-weil-functional-equation-sign`. Proposition
`prop-duality-reciprocity` supplies, for every $i$, the asserted
degreewise Laurent reciprocity. Proposition
*Parity of the functional-equation exponent* verifies that $d\chi/2$ is an
integer. Finally Proposition `prop-functional-equation` proves

$$
\varepsilon\in\{1,-1\},\qquad
Z(X_0,q^{-d}T^{-1})
=\varepsilon q^{d\chi/2}T^\chi Z(X_0,T)
$$

in $\mathbf Q(T)$. Hence all assertions of (v) follow.

The five independently verified clauses are exactly the conjunction stated
in the theorem.

Unresolved dependencies: def:weil-determinant-constants, def:weil-functional-equation-sign, prop:arithmetic-roots, prop:duality-reciprocity, prop:endpoints, prop:functional-equation, prop:integral-recovery
