+++
id = "sk-def-sf-weil-complexes"
kind = "section"
title = "Strict Weil complexes"
order = 2164
lean = ["AlgebraicGeometry.Etale.WeilComplex"]
+++
*Definition (sketch).*

A *strict Weil complex* at $\Lambda$ on $X=X_0\times_{k_0}k$ is a pair
$(K,\varphi)$ with $K\in\Dctf(X,\Lambda)$ and an isomorphism
$\varphi:Lg_\gamma^*K\xrightarrow{\sim}K$ for the geometric-Frobenius
automorphism $g_\gamma$; with morphisms the maps of underlying complexes
commuting with the $\varphi$'s, these form a category
$D^b_{ctf,\mathrm W}(X,\Lambda)$ with a forgetful functor. This is a category
of pairs over the underlying derived category, not a triangulated (derived)
category of Weil sheaves: its Hom-groups are not Ext groups of Weil sheaves
(a nonsplit Frobenius extension of $\Lambda$ by $\Lambda$, a Jordan block,
gives no nonzero map $\Lambda\to\Lambda[1]$ of pairs). Only traces, stalk
Frobenius maps, weights of cohomology sheaves, equivariant maps and
functorial triangles are used.

Uses: `def-trf-strict-weil-complex`
