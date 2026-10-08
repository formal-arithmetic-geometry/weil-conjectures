+++
id = "sk-p-dl-general-relative-line"
kind = "section"
title = "Direct images from a relative open affine line"
order = 2835
lean = ["AlgebraicGeometry.isMixedOfWeightsAtMost_higherLowerShriek_of_affineLine"]
uses = ["sk-d-dl-general-weights", "sk-i-dl-general-real", "sk-l-dl-a1-endpoints", "sk-l-dl-general-open-line", "sk-p-linear-filtration", "sk-prop-logdet", "sk-prop-sf-cbc", "sk-thm-sf-ctf-stability", "sk-thm-trace-transport"]
+++
*Proposition (sketch).*

Let $h_0:U_0\to Y_0$ be the projection from an open
$U_0\subset\mathbf A^1_{Y_0}$ whose geometric fibers are nonempty,
and let $F_0$ be lisse and pure of weight $w$.
Then $R^rh_{0!}F_0$ is mixed of weights at most $w+r$.

## Proof

For a closed point $y$ of residue cardinality $q_y$, base change gives

$$
(R^rh_{0!}F_0)_{\bar y}
\simeq H_c^r(U_{\bar y},F|_{U_{\bar y}}).
$$

Purity on the fiber is normalized by $q_y$, so
[sk-l-dl-general-open-line] gives the punctual upper bound.

To obtain mixedness, put $E_0=F_0\oplus(F_0^\vee\otimes T_w)$,
where $T_w$ is geometrically constant with Frobenius scalar mapping
to $q^w$ under $\iota$. Its two summands have conjugate local spectra,
so $E_0$ is real and pure of weight $w$. On each affine fiber,
$H_c^0=0$, $H_c^2$ is pure of weight $w+2$ by the endpoint lemma,
and $H_c^1$ has weights at most $w+1$. The trace formula gives a real
rational function

$$
L_\iota(U_y,E_0,T)=\frac{P_{1,y}(T)}{P_{2,y}(T)},
\qquad
P_{r,y}(T)=\iota\det(1-T\operatorname{Fr}_y\mid H_c^r(U_{\bar y},E)).
$$

The numerator roots have modulus at least $q_y^{-(w+1)/2}$, whereas
the denominator roots have modulus $q_y^{-(w+2)/2}$. Hence the factors
are coprime. Uniqueness of a reduced fraction with constant terms one
implies that both polynomials are real. Thus the constructible sheaves
$R^rh_{0!}E_0$ are real, and [sk-i-dl-general-real] makes them mixed.
Their direct summands $R^rh_{0!}F_0$ are mixed as well; the punctual
bounds already proved bound every pure quotient in a mixed filtration.

Uses: [sk-d-dl-general-weights], [sk-i-dl-general-real], [sk-l-dl-a1-endpoints], [sk-l-dl-general-open-line], [sk-prop-logdet], [sk-prop-sf-cbc], [sk-thm-sf-ctf-stability], [sk-thm-trace-transport]
