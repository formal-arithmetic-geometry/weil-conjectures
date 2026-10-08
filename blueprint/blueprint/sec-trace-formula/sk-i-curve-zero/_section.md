+++
id = "sk-i-curve-zero"
kind = "section"
title = "Zero-stalk vanishing on a smooth curve"
order = 2341
uses = ["sk-d-corr", "sk-d-curve-pieces", "sk-d-local-term", "sk-d-trace-class", "sk-p-pairing", "sk-thm-sf-package"]
lean = ["AlgebraicGeometry.ProEtale.GeometricOperations.localTerm_traceClass_eq_zero_of_isZero"]
+++
*Proposition (sketch).*

In the smooth-curve setting, if $K_{\bar x}=0$
then the local term $\LT_{\bar x}(\varphi_m)$ is
zero. The same holds for an arbitrary Frobenius coefficient morphism
$\Phi_m^*K\to K$.

## Proof

Write $c=(1,\Phi_m)$ for the graph correspondence and $u:\Phi_m^*K\to K$ for
the coefficient morphism ($\varphi_m$, or an arbitrary one). On an affine
chart with coordinates $t_i$ and $a_i=t_i(x)$ one has
$\Phi_m^*(t_i-a_i)=(t_i-a_i)^{q^m}$, so the fixed scheme is reduced and
finite and $\bar x$ is an isolated, open-and-closed, reduced component of
$\Fix(c)$; the local term $\LT_{\bar x}(u)$ of [sk-d-local-term] is thus
defined, without any invertibility of $u$.

The stalk at $\bar x$ of the trace-class source $\RHom_A(c_2^*K,c_1^!K)$ is
*not* $\RHom_A(K_{\bar x},K_{\bar x})$: restriction to a point does not
commute with internal Hom. For $K=j_!A$ on $\mathbf A^1$ with
$j:\gm\hookrightarrow\mathbf A^1$ one has $\RHom_A(j_!A,j_!A)\simeq Rj_*A$,
whose stalk at $0$ is $A$ in degree $0$ although $K_0=0$. So the vanishing
is not a formal consequence of locality on the fixed scheme. It is the
local-term theorem for contracting correspondences of
[Varshavsky, Def. 2.1.1 and Thm. 2.1.3](https://arxiv.org/abs/math/0505564),
the geometric input behind Fujiwara's theorem: if $c$ stabilizes a closed
subscheme $Z\subset X$ and is contracting near $Z$ — in the leg convention
of [sk-d-corr], where $u:c_2^*K\to c_1^!K$,

$$
c_2^{\cdot}(\mathcal I_Z)\subset c_1^{\cdot}(\mathcal I_Z)\,\mathcal O_C,
\qquad
c_2^{\cdot}(\mathcal I_Z)^n\subset c_1^{\cdot}(\mathcal I_Z)^{n+1}\,\mathcal O_C
\ \text{ for some }n\ge1
$$

— then on every open-and-closed part $\beta$ of $\Fix(c)$ meeting $Z$ the
trace class of $u$ coincides with the trace class of the correspondence
$u|_Z$ induced on $Z$, and so do the local terms. For the Frobenius graph
and $Z=\{\bar x\}$ this holds with $n=1$: $c_1=1$, and the generators
$t_i-a_i$ of $\mathcal I_{\bar x}$ pull back to their $q^m$-th powers, so
$\Phi_m^{\cdot}(\mathcal I_{\bar x})\,\mathcal O_X\subset\mathcal I_{\bar x}^{\,q^m}\subset\mathcal I_{\bar x}^{\,2}$
as $q^m\ge2$ (the induced map on the cotangent space at $\bar x$ is zero).
The correspondence induced on the point $\bar x$ is the identity
correspondence of $s$ with coefficient the stalk map
$u_{\bar x}:K_{\bar x}\to K_{\bar x}$, and the point normalization of
[sk-p-pairing] evaluates its local term to $\tr_A(u_{\bar x}\mid K_{\bar x})$.
Hence $\LT_{\bar x}(u)=\tr_A(u_{\bar x}\mid K_{\bar x})$, which is $0$ when
$K_{\bar x}=0$. Varshavsky's theorem is proved by specialization to the
normal cone of $Z$, for all $c$-morphisms and for our coefficient rings;
nothing is inverted, so the coefficient-morphism form follows at the same
time. Its proof reduces, through the localization trace additivity and the
proper pushforward compatibility of this chapter, exactly to the vanishing
asserted here, which is then established by the normal-cone argument; the
blueprint quotes that argument rather than the invalid stalk computation.

Uses: [sk-d-corr], [sk-d-curve-pieces], [sk-d-local-term], [sk-d-trace-class], [sk-p-pairing], [sk-thm-sf-package]
