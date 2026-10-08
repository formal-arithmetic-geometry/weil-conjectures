+++
id = "lem-weil-pbc-comparison-global-cohomology"
kind = "lemma"
title = "Comparison of global cohomology"
order = 1287
uses = ["def-weil-pbc-derived-categories", "def-weil-pbc-etale-cohomology", "def-weil-pbc-site-comparison-morphism", "prop-weil-pbc-site-comparison-finite-level", "thm-weil-pbc-site-comparison"]
+++
For finite $\Lambda$ and $K\in\Dplus(T_{\Et},\Lambda)$, the derived unit
induces a natural isomorphism

$$
 R\Gamma(T_{\Et},K)\xrightarrow{\sim}
 R\Gamma(T_{\Proet},\nu_T^*K).
$$

Both functors are ordinary derived sections.

## Proof

Since $\nu_T^*$ is exact by
[prop-weil-pbc-site-comparison-finite-level], its right adjoint $\nu_{T,*}$
in [def-weil-pbc-site-comparison-morphism] preserves injectives. For an
injective pro-etale resolution $J^\bullet$ of a bounded-below complex,
$\nu_{T,*}J^\bullet$ therefore computes its derived direct image and the
subsequent derived sections. Underived evaluation on the final object gives
$\Gamma(T_{\Et},\nu_{T,*}J^r)=\Gamma(T_{\Proet},J^r)$. Thus
$R\Gamma_{\Et}R\nu_{T,*}=R\Gamma_{\Proet}$. Apply this identity to the
derived unit, which is an isomorphism by [thm-weil-pbc-site-comparison].
