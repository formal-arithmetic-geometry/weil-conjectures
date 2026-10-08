+++
id = "def-kun-rgamma-unbounded"
kind = "definition"
title = "Unbounded derived global sections"
order = 1661
uses = ["def-weil-pbc-etale-cohomology", "def-weil-pbc-kinjective-resolutions", "prop-weil-pbc-kinjective-resolutions-exist"]
+++
For a scheme $T$, a commutative ring $\Lambda$ and
$K\in D(T_{\Et},\Lambda)$, choose a K-injective resolution in the
sense of [def-weil-pbc-kinjective-resolutions],
$K\to I$ (which exists by
[prop-weil-pbc-kinjective-resolutions-exist]) and put

$$
\RGamma(T_{\Et},K)=\Gamma(T_{\Et},I),
\qquad
H^q(T_{\Et},K)=\mathcal H^q(\RGamma(T_{\Et},K)).
$$

The independence of the result of the chosen resolution is
recorded with the other properties of this construction, and for
$K\in\Dplus(T_{\Et},\Lambda)$ its agreement with the functor
$\RGamma(T_{\Et},-)$ of
[def-weil-pbc-etale-cohomology] is
also recorded with those properties.
