+++
id = "lem-trf-integration-component-sum"
kind = "lemma"
title = "Integration splits over the open–closed components"
order = 2348
uses = ["def-trf-coefficient-conventions", "def-trf-dualizing-complex", "def-trf-fixed-scheme", "def-trf-integration", "def-trf-local-term", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "prop-functor-package", "thm-trf-dualizing-complex-composition"]
+++
Fix the coefficient
conventions, $A=A_{E,n}$, $s=\Spec k$, and let $T$ be a
separated finite-type scheme over $s$ which is a finite disjoint union

$$
T=\coprod_{\beta\in B}\beta
$$

of open-and-closed subschemes $j_\beta:\beta\hookrightarrow T$, each
proper over $s$. Then $T$ is proper over $s$. For
$\tau:A_T\to\omega_{T,A}$ and $\beta\in B$ define the *restriction*

$$
\tau|_\beta:
A_\beta\xrightarrow{\ \sim\ }Lj_\beta^*A_T
\xrightarrow{Lj_\beta^*\tau}Lj_\beta^*\omega_{T,A}
\cong Rj_\beta^!\omega_{T,A}\cong\omega_{\beta,A},
$$

using the equality $Rj_\beta^!\cong Lj_\beta^*$ for the open immersion
$j_\beta$ ([prop-functor-package], item (6), relative dimension $0$)
and the identification of [thm-trf-dualizing-complex-composition]
(this restriction makes sense without any properness). Then

$$
\int_T\tau=\sum_{\beta\in B}\int_\beta(\tau|_\beta),
$$

where $\int_T,\int_\beta$ are the integrations of
[def-trf-integration] and $\omega_{T,A}$ is the
dualizing complex of
[def-trf-dualizing-complex]; for $B=\emptyset$ both sides are $0$.
In particular, if $c$ is an admissible correspondence whose fixed
scheme $F=\operatorname{Fix}(c)$ of [def-trf-fixed-scheme] has
finitely many open-and-closed components $\beta\in\pi_0(F)$, each
proper over $s$, then $F$ is proper and
$\int_F\tau=\sum_{\beta\in\pi_0(F)}\int_\beta(\tau|_\beta)$, the
restrictions being those of [def-trf-local-term].

## Proof

*Properness.* The morphism $a_T:T\to s$ is separated and of finite
type. It is universally closed: for any $s'\to s$ the base change
$T_{s'}=\coprod_\beta\beta_{s'}$ is a finite disjoint union of
open-and-closed pieces, a closed subset $Z\subseteq T_{s'}$ is the
finite union of the closed subsets $Z\cap\beta_{s'}$ of the
$\beta_{s'}$, and its image in $s'$ is the finite union of their
images, which are closed because each $\beta\to s$ is universally
closed. Hence $T$ is proper over $s$ and $\int_T$ of
[def-trf-integration] is defined.

*Splitting.* The pro-etale site of a disjoint union of schemes is the
disjoint union of the sites ([def-weil-pbc-proetale-site]), so
$D(T,A)\cong\prod_{\beta}D(\beta,A)$ via $(Lj_\beta^*)_\beta$, and the
six operations decompose
accordingly: in particular
$R\Gamma(T,-)\cong\prod_\beta R\Gamma(\beta,-)$ (the product is a direct
sum over the finite set $B$),
the unit $A\to R\Gamma(T,A_T)$ of [def-trf-integration] is the
tuple of the units of the components, and the counit
$\varepsilon_{a_T}$ is the tuple of the counits
$\varepsilon_{a_\beta}$ (the adjunctions of [def-trf-integration]
decompose with the products, by the compatibility of the six-functor
formalism with disjoint unions; here $a_\beta=a_Tj_\beta$ and
$Rj_\beta^!=Lj_\beta^*$). Under this decomposition $\omega_{T,A}$
corresponds to the tuple of the $Lj_\beta^*\omega_{T,A}\cong
\omega_{\beta,A}$ of [thm-trf-dualizing-complex-composition], and
$\tau$ to the tuple of its restrictions $\tau|_\beta$ defined above.
Hence the composite displayed in
[def-trf-integration] for $\int_T\tau$ is the tuple of the
composites defining the $\int_\beta(\tau|_\beta)$; the unit
$A\to\bigoplus_\beta R\Gamma(\beta,A_\beta)$ is the diagonal and the
counit $\bigoplus_\beta R\Gamma(\beta,\omega_{\beta,A})\to A$ is the sum
map, so the composite is the sum of the component composites, which is
the displayed identity. If $B=\emptyset$ then $T=\emptyset$,
$R\Gamma(T,-)=0$ and both sides vanish.

*The fixed-scheme case.* For $T=F$ and $B=\pi_0(F)$, finite by
hypothesis ([def-trf-fixed-scheme]), the restriction $\tau|_\beta$
above is literally the composite used in [def-trf-local-term], so the
last assertion is the special case just proved.
