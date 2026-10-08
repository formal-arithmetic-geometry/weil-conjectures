+++
id = "def-wf-lie-algebra-derivation"
kind = "definition"
title = "Tangent spaces, Lie algebras and rational actions"
order = 2481
uses = ["def-wf-algebraic-representations", "def-wf-lie-algebra"]
lean = ["AlgebraicGeometry.tangentGroup", "Matrix.GeneralLinearGroup.lieAlgebra", "Matrix.GeneralLinearGroup.RationalHom", "Matrix.GeneralLinearGroup.RationalHom.differential"]
+++
*Tangent spaces and differentials.* Let $X=\operatorname{Spec}A$ be a
finite-type affine $k$-scheme (for instance an affine variety, i.e.
$A$ finitely generated and reduced) and let $x\in X(k)$, with maximal
ideal $\mathfrak m_x\subseteq A$ of the functions vanishing at $x$. The
*tangent space* of $X$ at $x$ is

$$
T_xX=(\mathfrak m_x/\mathfrak m_x^2)^\vee
=\operatorname{Hom}_k(\mathfrak m_x/\mathfrak m_x^2,k).
$$

Equivalently, $T_xX$ is the set of $k$-algebra maps
$A\to k[\varepsilon]/\varepsilon^2$ reducing to evaluation at $x$
modulo $\varepsilon$: such a map is $f\mapsto f(x)+\varepsilon\,v(f)$
with $v$ a $k$-derivation at $x$, and $v\mapsto v|_{\mathfrak m_x}$
identifies these derivations with the linear forms on $\mathfrak m_x$
killing $\mathfrak m_x^2$ (the Leibniz rule forces
$v(\mathfrak m_x^2)=0$ and $v(1)=0$, and conversely every such form
extends uniquely via $A=k\oplus\mathfrak m_x$). A regular map
$\varphi:X\to Y$ with comorphism $\varphi^*:B\to A$ satisfies
$\varphi^*\mathfrak m_{\varphi(x)}\subseteq\mathfrak m_x$, hence induces
$\mathfrak m_{\varphi(x)}/\mathfrak m_{\varphi(x)}^2\to
\mathfrak m_x/\mathfrak m_x^2$; the dual linear map
$d\varphi_x:T_xX\to T_{\varphi(x)}Y$ is the *differential* of $\varphi$
at $x$. In the dual-number description it is composition with
$\varphi^*$; in particular $d(\psi\circ\varphi)_x=d\psi_{\varphi(x)}\circ
d\varphi_x$.

*Lie algebra of a matrix group.* Let $G\subseteq\operatorname{GL}(V)$ be
a closed subgroup scheme of finite type (see the last paragraph), for
example a smooth matrix group. For a commutative $k$-algebra $R$, the
$R$-points $G(R)$ are the matrices in $\operatorname{GL}(V\otimes_kR)$
satisfying the defining equations of $G$ over $R$. Its *Lie algebra* is
$\operatorname{Lie}(G)=T_1G$; by the dual-number description, and
identifying $T_1\operatorname{GL}(V)=\operatorname{End}(V)$ through
$X\mapsto1+\varepsilon X$,

$$
\operatorname{Lie}(G)=\{X\in\operatorname{End}(V):
1+\varepsilon X\in G(k[\varepsilon]/\varepsilon^2)\},
$$

a Lie algebra in the sense of [def-wf-lie-algebra] under the bracket
$[X,Y]=XY-YX$ of $\operatorname{End}(V)$. (That this subspace is
closed under the bracket, and that $dr$ below preserves brackets, is standard: compare
Milne, *Algebraic Groups* (2017), Chapter 10.)

*Rational actions.* A *rational representation* of $G$ is a regular
homomorphism $r:G\to\operatorname{GL}(M)$, i.e. an algebraic-group
module in the sense of [def-wf-algebraic-representations]. Its
differential at $1$ is the linear map
$dr:\operatorname{Lie}(G)\to\operatorname{End}(M)$ characterized by
$r(1+\varepsilon X)=1+\varepsilon\,dr(X)$ over
$k[\varepsilon]/\varepsilon^2$; it is a Lie representation of
$\operatorname{Lie}(G)$ on $M$ in the sense of [def-wf-lie-algebra],
i.e. $dr([X,Y])=dr(X)dr(Y)-dr(Y)dr(X)$. The *adjoint action*
is $\operatorname{Ad}(g)X=gXg^{-1}$ for $g\in G(k)$, preserving
$\operatorname{Lie}(G)$ because conjugation by $g$ preserves $G$; its
differential is $\operatorname{ad}(Y)X=[Y,X]$, since over
$k[\varepsilon]/\varepsilon^2$ one has
$(1+\varepsilon Y)X(1+\varepsilon Y)^{-1}=X+\varepsilon(YX-XY)$.

*Matrix group schemes and smoothness.* A *finite-type matrix group
scheme* is a closed subscheme $\mathcal G\subseteq\operatorname{GL}(V)$
cut out by a finitely generated, possibly nonradical, ideal, such that
the regular multiplication and inversion of $\operatorname{GL}(V)$
restrict to it; its coordinate algebra need not a priori be reduced,
and its tangent spaces and Lie algebra are defined by the same formulas
as above, directly from the defining equations. For a closed point $x$
of a finite-type affine $k$-scheme $X=\operatorname{Spec}A$, the *local
ring* is $\mathcal O_{X,x}=A_{\mathfrak m_x}$; it is *regular* if
$\dim_kT_xX=\dim\mathcal O_{X,x}$ (Krull dimension; the inequality
$\ge$ always holds), and $X$ is *smooth over $k$ at $x$* when
$\mathcal O_{X,x}$ is regular ($k$ being algebraically closed of
characteristic zero, hence perfect). A *smooth matrix group* is a
matrix group smooth at every closed point.
