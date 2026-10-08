+++
id = "def-weil-pbc-proetale-operations"
kind = "definition"
title = "Derived operations on ringed pro-etale topoi"
order = 1234
uses = ["def-weil-pbc-kinjective-resolutions", "def-weil-pbc-proetale-modules", "def-weil-pbc-proetale-site"]
+++
Let $u:U\to V$ be a morphism and let $R_V$ be a coefficient sheaf whose
inverse image is identified with $R_U$. The module inverse image is

$$
 u^*F=u^{-1}F\otimes_{u^{-1}R_V}R_U.
$$

Using a functorial K-flat and K-injective resolution
[def-weil-pbc-kinjective-resolutions] defines ordinary triangulated functors

$$
 Lu^*:D(V_{\Proet},R_V)\longrightarrow D(U_{\Proet},R_U),
 \qquad
 Ru_*:D(U_{\Proet},R_U)\longrightarrow D(V_{\Proet},R_V),
$$

with $Lu^*\dashv Ru_*$.
