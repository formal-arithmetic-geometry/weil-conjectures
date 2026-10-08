+++
id = "sk-d-curve-pieces"
kind = "section"
title = "Curve coefficient pieces"
order = 2339
uses = ["sk-d-proper-pushforward", "sk-d-setup", "sk-d-six", "sk-d-weil"]
lean = ["AlgebraicGeometry.ProEtale.WeilComplex.curvePieces"]
+++
*Definition (sketch).*

Let a Weil datum have $X_0$ smooth of pure
dimension one. Fix $m\ge1$ and
$x\in X_0(\mathbf F_{q^m})$. On $X$ let $i:\{\bar x\}\hookrightarrow X$
and $j:U=X\setminus\{\bar x\}\hookrightarrow X$.
Set $K^Z=Ri_*i^*K$ and $K^U=j_!j^*K$ using the
geometric operations.
On the graph $(1,\Phi_m)$, let $u^Z=[i,i]_!(F_{x,m})$ be the
proper pushforward of the stalk map.
Let $u^U$ be the composite

$$
\Phi_m^*j_!j^*K\simeq j_!\Phi_{m,U}^*j^*K
\xrightarrow{j_!j^*\varphi_m}j_!j^*K.
$$

The first isomorphism is open $!$-base change. These are the induced
maps on the two pieces of the functorial localization triangle.
The construction also applies to a Frobenius coefficient morphism in
the sense of [sk-d-weil].

Uses: [sk-d-proper-pushforward], [sk-d-setup], [sk-d-six], [sk-d-weil]
