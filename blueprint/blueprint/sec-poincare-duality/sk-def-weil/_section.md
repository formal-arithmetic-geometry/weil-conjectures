+++
id = "sk-def-weil"
kind = "section"
title = "Weil structures and their Frobenius normalization"
order = 2423
uses = ["sk-def-ops"]
lean = ["AlgebraicGeometry.ProEtale.WeilComplex"]
+++
*Definition (sketch).*

In the setting of [sk-def-set], let $g_\gamma$ be the geometric
Frobenius automorphism and let $\Lambda(r)$ be the Tate twist, on which
geometric Frobenius acts by $q^{-r}$ (hence $q^{r}$ on
$\Lambda(-r)$). A *strict Weil complex* is a pair
$(K,\varphi_K)$ with $\varphi_K:Lg_\gamma^*K\cong K$, morphisms being
maps of the underlying complexes commuting with the $\varphi$'s. This is a
category of pairs over the underlying derived category, not a triangulated
(derived) category of Weil sheaves: its Hom-groups are not Ext groups of
Weil sheaves (a nonsplit Frobenius extension of $\Lambda$ by $\Lambda$, a
Jordan block, gives no nonzero map $\Lambda\to\Lambda[1]$ of pairs). Only
traces, stalk Frobenius maps, weights of cohomology sheaves, equivariant maps
and functorial triangles are used. The
*contragredient datum* on $K^\vee$ is
$\varphi_{K^\vee}=R\mathcal H om(\varphi_K^{-1},\varphi_\Lambda)\circ (\text{pullback})$, and $\varphi_{K^\vee(r)}=\varphi_{K^\vee}\otimes\tau_r$.
(Blueprint 15, def:pod-dual-tate-datum.)

Uses: [sk-def-ops]
