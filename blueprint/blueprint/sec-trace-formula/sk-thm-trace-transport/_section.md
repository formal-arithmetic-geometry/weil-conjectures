+++
id = "sk-thm-trace-transport"
kind = "section"
title = "Transport of the trace formula to the non-finite stages"
order = 2394
uses = ["sk-d-setup", "sk-d-six", "sk-d-trace", "sk-d-weil", "sk-def-sf-weil-complexes", "sk-i-curve-zero", "sk-p-trace-coeff", "sk-prop-cd", "sk-prop-logdet", "sk-prop-trace-adic", "sk-thm-sf-ctf-stability", "sk-thm-trace-formula"]
lean = ["AlgebraicGeometry.ProEtale.trace_globalOperator_eq_sum_and_eulerProduct"]
+++
*Theorem (sketch).*

Let the coefficient ring range over the three non-finite stages

$$
\Lambda\in\{\mathcal O_E,\ E,\ \overline{\mathbf Q}_\ell\},
$$

the $\mathcal O_E$-stage being the normalized systems of
finite-level objects, the $E$-stage its
rationalization, and the $\overline{\mathbf Q}_\ell$-stage the colimit over
finite $E/\mathbf Q_\ell$. Let $X_0/\mathbf F_q$ be separated of finite
type and let $K$ be a Weil datum with coefficients in
$\Lambda$, that is, a Weil pair at the stage $\Lambda$ in the all-stage
sense of [sk-def-sf-weil-complexes]: at $\mathcal O_E$ a normalized system
of finite-level Weil pairs ([sk-d-weil]) whose transitions commute with the
$\varphi_n$ (a compatible tower of Weil pairs as in
[sk-prop-trace-adic](ii)), and at $E$ and $\overline{\mathbf Q}_\ell$ its
rationalization and colimit. Then:

1. **(a)** *Trace identity.* The identity of
[sk-thm-trace-formula] holds for every $m\ge1$ with $A$ replaced by
$\Lambda$, with compact cohomology and
ordinary traces taken at the stage $\Lambda$.
1. **(b)** *Euler-product form.* Let
$\Lambda\in\{E,\overline{\mathbf Q}_\ell\}$, write $e_x$ for the degree of
a closed point $x\in|X_0|$, and put
$$
L(X_0,K,T)=\prod_{x\in|X_0|}
\det\bigl(1-T^{e_x}F_x\mid K_{\bar x}\bigr)^{-1}
\in1+T\Lambda[[T]],
$$
a locally finite product. For a complex, the stalk determinant denotes
the alternating product of the determinants on its cohomology. Then
$$
L(X_0,K,T)=\prod_{i}
\det\bigl(1-TF\mid H_c^i(X,K)\bigr)^{(-1)^{i+1}}
$$
as formal power series, the product being finite; if $X_0$ is a curve and $K$ is a sheaf in degree zero, it
runs over $0\le i\le2$. Any field embedding
$\iota:\overline{\mathbf Q}_\ell\to\mathbf C$ carries the identity to one
in $\mathbf C[[T]]$.

## Proof

*Step 1 (the finite levels).* At $\Lambda=A_{E,n}$, clause (a) is
[sk-thm-trace-formula]. Its coefficient-morphism variant also applies
to noninvertible maps, under the explicit curve input above; Steps 2–3
preserve this variant.

*Step 2 (compatibility with the reductions).* By [sk-p-trace-coeff], both sides commute with
$(-)\otimes^{\mathrm L}_{A_{E,n}}A_{E,m}$: compact cohomology and the
geometric stalks are compatible with finite reduction of the coefficient
ring, the Frobenius structure of [sk-d-weil] reduces with them, and the
ordinary trace of [sk-d-trace] on a perfect complex is compatible with
base change of the coefficient ring. So the identities of Step 1 form a
compatible system over the tower.

*Step 3 (the adic stage).* Write $C_n=R\Gamma_c(X,K_n)$.
By [sk-thm-sf-ctf-stability], each $C_n$ is perfect, and Step 2 gives
$C_n\otimes^{\mathrm L}_{A_{E,n}}A_{E,1}\simeq C_1$.
To see that the Tor-amplitudes are uniform, choose a bounded finite-free
model of $C_n$ over the Artinian local ring $A_{E,n}$. Whenever a
differential has a unit entry, split off the resulting contractible
two-term summand. The remaining minimal complex has zero differential
after reduction to the residue field $A_{E,1}$. Its ranks are therefore
the dimensions of $H^i(C_1)$, and its terms vanish outside the fixed
cohomological range of $C_1$. The same argument applies to each stalk
tower. Thus the perfect-realization input in [sk-prop-trace-adic] applies
over $\mathcal O_E$. The realized traces reduce to the finite-level
traces; completeness of $\mathcal O_E$ now gives (a) from Step 2.

*Step 4 (the field stages).* The map $\mathcal O_E\to E$ is flat and
the trace of an endomorphism of a perfect complex commutes with flat
extension of the coefficient ring, so (a) holds over $E$ for the
rationalization of a lattice. A $\overline{\mathbf Q}_\ell$-object is
represented over some finite $E/\mathbf Q_\ell$, and traces are compatible
with $E\hookrightarrow\overline{\mathbf Q}_\ell$; this gives (a) at the
last stage. If a field-stage Weil map is only defined after inverting
$\varpi$, clear its denominators on a finite coefficient model, as in
[sk-prop-trace-adic]. Multiplication of the one-step map by $c\ne0$
multiplies its $m$-th iterate and both traces by $c^m$. Apply the
integral formula and divide by $c^m$.

*Step 5 (from (a) to (b)).* Group the points of
$X_0(\mathbf F_{q^m})$ by the closed points below them: a closed point $x$
of degree $e_x$ contributes $e_x$ rational points exactly when
$e_x\mid m$, each with stalk trace $\tr(F_x^{m/e_x}\mid K_{\bar x})$.
Multiply (a) by $T^m/m$, sum over $m\ge1$ and exponentiate. In
characteristic zero

$$
\exp\Bigl(\sum_{m\ge1}\tr(F^m\mid V)\,\frac{T^m}{m}\Bigr)
=\det(1-TF\mid V)^{-1}
$$

for an endomorphism of a finite-dimensional vector space; applied on the
point side it produces the local factors
$\det(1-T^{e_x}F_x\mid K_{\bar x})^{-1}$, hence $L(X_0,K,T)$, and applied
to each $H_c^i$ it produces the alternating product of determinants. The
groups $H_c^i(X,K)$ are finite dimensional and vanish outside a bounded
range by [sk-thm-sf-ctf-stability], so the product is finite; for a curve and a coefficient sheaf in degree zero,
compactification by [sk-thm-nagata-compactification], extension by zero and
[sk-prop-cd] give the range $0\le i\le2$.

*Step 6 (the embedding).* A field embedding $\iota$ is a ring
homomorphism, so it carries the identity in
$\overline{\mathbf Q}_\ell[[T]]$ coefficientwise to one in
$\mathbf C[[T]]$.

Uses: [sk-d-setup], [sk-d-six], [sk-d-trace], [sk-d-weil], [sk-def-sf-weil-complexes], [sk-i-curve-zero], [sk-p-trace-coeff], [sk-prop-cd], [sk-prop-logdet], [sk-prop-trace-adic], [sk-thm-sf-ctf-stability], [sk-thm-trace-formula]
