+++
id = "prop-weil-pbc-proetale-constant-ring-map"
kind = "theorem"
title = "Constant coefficients on the pro-etale site"
order = 1235
uses = ["def-weil-pbc-inverse-image", "def-weil-pbc-proetale-modules", "def-weil-pbc-proetale-site", "def-weil-pbc-scheme-conventions"]
tags = ["latex:proposition"]
+++
Let $\Lambda$ be a finite discrete ring and let $u:U\to V$ be a morphism
[def-weil-pbc-scheme-conventions] of schemes, with $\Lambda_{V,\Proet}$ and
$\Lambda_{U,\Proet}$ the sheaves of [def-weil-pbc-proetale-modules] on the
small pro-etale sites [def-weil-pbc-proetale-site]. Then the structure map

$$
 u^{-1}\Lambda_{V,\Proet}\longrightarrow\Lambda_{U,\Proet}
$$

is an isomorphism.

## Proof

By [def-weil-pbc-proetale-modules] the sheaf $\Lambda_{T,\Proet}$ is the
sheafification of $U\mapsto\operatorname{Cont}(\pi_0(|U|),\Lambda)$;
decomposing a pro-etale object into its clopen connected components, which
form a covering in the small pro-etale topology
[def-weil-pbc-proetale-site], identifies $\Lambda_{T,\Proet}$ with the free
$\Lambda$-module sheaf of rank one, so that

$$
 \operatorname{Hom}\bigl(\Lambda_{T,\Proet},G\bigr)=G(T)
$$

for every sheaf $G$ of $\Lambda$-modules on $T_{\Proet}$, naturally in $G$.
By [def-weil-pbc-inverse-image] the inverse image is the sheafification of
the presheaf inverse image, hence left adjoint to the direct image, and
adjunction therefore gives a natural bijection

$$
 \operatorname{Hom}\bigl(u^{-1}\Lambda_{V,\Proet},G\bigr)
 \cong\operatorname{Hom}\bigl(\Lambda_{V,\Proet},u_*G\bigr)
 \cong(u_*G)(V)=G(U)
 \cong\operatorname{Hom}\bigl(\Lambda_{U,\Proet},G\bigr)
$$

for every sheaf $G$ of $\Lambda$-modules on $U_{\Proet}$. The composite is
the map induced by the displayed structure morphism, which is consequently an
isomorphism by the Yoneda lemma.
