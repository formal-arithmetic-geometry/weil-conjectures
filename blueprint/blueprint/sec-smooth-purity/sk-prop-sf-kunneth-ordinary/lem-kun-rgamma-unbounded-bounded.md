+++
id = "lem-kun-rgamma-unbounded-bounded"
kind = "lemma"
title = "Agreement with the bounded derived global sections"
order = 1663
uses = ["def-kun-rgamma-unbounded", "def-weil-pbc-etale-cohomology", "prop-weil-pbc-kinjective-resolutions-exist"]
+++
Let $T$ be a scheme, $\Lambda$ a commutative ring and
$K\in\Dplus(T_{\Et},\Lambda)$. Then $\RGamma(T_{\Et},K)$ of
[def-kun-rgamma-unbounded] agrees canonically with
$\Gamma(T,\operatorname{Kinj}(K))$ of
[def-weil-pbc-etale-cohomology].

## Proof

The object $\RGamma(T_{\Et},K)$ of
[def-kun-rgamma-unbounded] is $\Gamma(T_{\Et},I)$ for a
K-injective resolution $K\to I$, while
[def-weil-pbc-etale-cohomology] uses the functorial K-injective
resolution $\operatorname{Kinj}(K)$. The two resolutions are
chain-homotopy equivalent, and the comparison between them is a
homotopy equivalence, by
[prop-weil-pbc-kinjective-resolutions-exist]; applying
$\Gamma(T_{\Et},-)$ therefore gives a canonical isomorphism in
$D(\Lambda)$.
