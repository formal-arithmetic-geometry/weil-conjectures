+++
id = "sk-p-frob"
kind = "section"
title = "Frobenius local terms on smooth curves"
order = 2355
uses = ["sk-d-curve-pieces", "sk-d-integral", "sk-d-local-term", "sk-d-proper-pushforward", "sk-d-trace", "sk-d-weil", "sk-i-additivity", "sk-i-curve-zero", "sk-p-local", "sk-p-proper", "sk-thm-sf-package"]
lean = ["AlgebraicGeometry.ProEtale.GeometricOperations.localTerm_traceClass_eq_trace"]
+++
*Proposition (sketch).*

For the smooth-curve datum, the
local term at $\bar x$ is

$$
\LT_{\bar x}(\varphi_m)=
\hyperref[sk-d-trace]{\tr_A}(F_{x,m}\mid K_{\bar x}).
$$

No local constancy of $K$ at $\bar x$ is assumed.

## Proof

On an affine chart, the fixed algebra is the quotient by
$t_i^{q^m}-t_i$. The Chinese remainder decomposition of these
polynomials makes it a finite product of copies of $k$, with factors
indexed by the rational points of [sk-d-weil]. The monomials
$\prod_i t_i^{e_i}$ with $0\le e_i<q^m$ generate each affine
coordinate algebra over the image of Frobenius. Thus $\Phi_m$ is
finite, hence proper, as required by [sk-d-operator]. Each fixed point
is a reduced clopen component. At $x$, with $a_i=t_i(x)$, one has
$\Phi_m^*(t_i-a_i)=(t_i-a_i)^{q^m}$. Consequently the induced map on
the cotangent space is zero, i.e. the graph correspondence $(1,\Phi_m)$
is contracting near $\bar x$ in the sense used in [sk-i-curve-zero];
that contracting property, not a stalk computation, is what makes the
local terms of this correspondence computable from stalks.

Use the pieces of [sk-d-curve-pieces]. The open piece
$K^U=j_!j^*K$ is an extension by zero across the closed point $\bar x$,
so $(K^U)_{\bar x}=0$ by the stalk computation in the open–closed
triangle of [sk-prop-sf-open-closed-triangle], and [sk-i-curve-zero]
kills its local term. For that application, base change $X_0$ to
$\mathbf F_{q^m}$ and use $u^U$ as the one-step Weil map; the chosen
point is rational over this field. By [sk-i-additivity], only the closed piece
remains. The two vertical maps $i,i$ are proper. Apply [sk-p-proper]
to the point correspondence. Its map on fixed supports is the
inclusion of $\bar x$, and its coefficient map is exactly
$i^*K\simeq i^*\Phi_m^*K\xrightarrow{i^*\varphi_m}i^*K$.
Proper integration and point normalization in [sk-p-local] give
the trace asserted in [sk-d-local-term].

Uses: [sk-d-curve-pieces], [sk-d-local-term], [sk-d-trace], [sk-d-weil], [sk-i-additivity], [sk-i-curve-zero], [sk-p-local], [sk-p-proper], [sk-thm-sf-package]
