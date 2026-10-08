+++
id = "sk-thm-sf-pf-finite"
kind = "section"
title = "Projection formula, finite coefficients"
order = 1877
uses = ["sk-def-sf-exchanges"]
lean = ["AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_rightDerivedLowerShriek"]
+++
*Theorem (sketch).*

Let $\Lambda=A_{E,n}$, let $f:X\to Y$ be separated of finite type, and let
$K$ and $L$ be bounded constructible complexes on the small étale sites with
$L$ of finite Tor amplitude, so that $K\in\Dbc(X,\Lambda)$ and
$L\in\Dctf(Y,\Lambda)$. Then $\operatorname{PF}_{f,K,L}$ is an isomorphism in
$D^+(Y_{\Et},\Lambda)$, natural in $K$ and $L$.

## Proof

Split off a compactification $f=\bar f\circ j$; the projection transformation is
then the direct-image projection map for $\bar f$ composed with the
identification $j_!K\otimes^L\bar f^*L\cong j_!(K\otimes^Lf^*L)$, which is
checked on étale stalks. For a geometric point $\bar y$ of $Y$, compact-support
base change identifies the stalk of the projection map with
$R\Gamma_c(X_{\bar y},K^{\mathrm{fib}}_{\bar y})\otimes^LP\to R\Gamma_c(X_{\bar y},K^{\mathrm{fib}}_{\bar y}\otimes^L\underline P)$. The
fibrewise map is an isomorphism for every $P$: choose a bounded complex of
finite free modules representing $P$; both sides are exact functors of $P$
agreeing on $P=\Lambda$ (the unit identification), and the class of $P$ for
which the map is an isomorphism is closed under finite sums, shifts, cones and
direct summands. Hence all geometric stalks of the cone vanish, and geometric
stalks are conservative on the étale site.

Uses: `\Cref{sk-def-sf-exchanges}`, `def-compact-support-direct-image-detailed`, `lem-weil-finite-compact-projection-formula`
