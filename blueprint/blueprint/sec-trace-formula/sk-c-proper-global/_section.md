+++
id = "sk-c-proper-global"
kind = "section"
title = "Proper global trace comparison"
order = 2343
uses = ["sk-d-corr", "sk-d-integral", "sk-d-operator", "sk-d-proper-pushforward", "sk-d-six", "sk-d-trace", "sk-d-trace-class", "sk-p-pairing", "sk-p-proper", "sk-thm-sf-package"]
lean = ["AlgebraicGeometry.ProEtale.GeometricOperations.trace_globalOperator_eq_integral_traceClass"]
+++
*Corollary (sketch).*

Let $X$ be proper over $s$, $K\in D^b_{ctf}(X,A)$, and let
$(C,c,u)$ have proper ordinary leg $c_2$.
With compact cohomology, its
global operator satisfies

$$
\hyperref[sk-d-trace]{\tr_A}\bigl(T_c(u)\mid R\Gamma_c(X,K)\bigr)
=\hyperref[sk-d-integral]{\int_{\Fix(c)}}\hyperref[sk-d-trace-class]{\Tr_c(u)}.
$$

## Proof

The support $C$ is proper since $a_C=a_Xc_2$ is proper; the fixed scheme
of [sk-d-corr] is closed in $C$ since $X$ is separated.
Use the construction in [sk-d-proper-pushforward] for $(a_X,a_C)$
and apply [sk-p-proper]. By composition of adjunctions in
[sk-thm-sf-package], the pushed coefficient map is exactly [sk-d-operator].
On fixed supports the pushforward is [sk-d-integral].
The point normalization in [sk-p-pairing] identifies the pushed trace
class with the ordinary trace of that operator.

Uses: [sk-d-corr], [sk-d-integral], [sk-d-operator], [sk-d-proper-pushforward], [sk-d-six], [sk-d-trace-class], [sk-d-trace], [sk-p-pairing], [sk-p-proper], [sk-thm-sf-package]
