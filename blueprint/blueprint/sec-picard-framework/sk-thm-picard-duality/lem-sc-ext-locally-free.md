+++
id = "lem-sc-ext-locally-free"
kind = "lemma"
title = "Ext of a finite locally free module"
order = 689
uses = ["def-sc-ext-sheaf"]
+++
Let $X$ be a scheme, $\mathcal F$ a finite locally free
$\mathcal O_X$-module and $\mathcal G$ an $\mathcal O_X$-module,
with $\operatorname{Ext}$ as in [def-sc-ext-sheaf] and
$\mathcal F^{\vee}=\mathcal{H}om_{\mathcal O_X}(\mathcal F,\mathcal O_X)$. Then there are canonical isomorphisms

$$
\operatorname{Ext}^i_X(\mathcal F,\mathcal G)\;\cong\;
\mathrm H^i\bigl(X,\mathcal F^{\vee}\otimes_{\mathcal O_X}
\mathcal G\bigr)\qquad(i\geq0),
$$

in particular
$\operatorname{Ext}^i_X(\mathcal O_X,\mathcal G)=\mathrm H^i(X,\mathcal G)$.

## Proof

For finite locally free $\mathcal F$ the evaluation map
$\mathcal F^{\vee}\otimes_{\mathcal O_X}-\to \mathcal{H}om_{\mathcal O_X}(\mathcal F,-)$ is an isomorphism, so
$\operatorname{Hom}_{\mathcal O_X}(\mathcal F,\mathcal G)=\Gamma \bigl(X,\mathcal F^{\vee}\otimes\mathcal G\bigr)$ and the functor
$\operatorname{Hom}_{\mathcal O_X}(\mathcal F,-)$ is the composite
of the exact functor $\mathcal F^{\vee}\otimes-$
(a tensor product with a locally free module is exact) with the
global sections functor $\Gamma(X,-)$. The higher derived
functors of such a composite are the derived functors of
$\Gamma(X,-)$ evaluated at $\mathcal F^{\vee}\otimes\mathcal G$
(standard homological algebra: an exact functor followed by a
left-exact functor has the composed derived functors in each
degree), which is $\mathrm H^i(X,\mathcal F^{\vee}\otimes\mathcal G)$; taking $\mathcal F=\mathcal O_X$, whose dual is
$\mathcal O_X$, gives the last assertion, with
$\operatorname{Ext}$ of [def-sc-ext-sheaf].
