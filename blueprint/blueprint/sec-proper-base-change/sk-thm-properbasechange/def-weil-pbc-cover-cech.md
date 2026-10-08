+++
id = "def-weil-pbc-cover-cech"
kind = "definition"
title = "Covering Cech complexes"
order = 1281
uses = ["def-weil-pbc-etale-sheaves", "def-weil-pbc-proetale-modules"]
+++
For a finite covering $\mathcal V=\{V_a\to U\}_{a=1}^m$ on either site and a
module sheaf $M$, its Cech cochain complex has

$$
 \check C^p(\mathcal V,M)=
 \prod_{a_0,\ldots,a_p}M(V_{a_0}\times_U\cdots\times_UV_{a_p}),
 \qquad \delta=\sum_{j=0}^{p+1}(-1)^j d_j^*.
$$

Its cohomology is denoted $\check H^p(\mathcal V,M)$. The augmentation is
restriction from $M(U)$. Here module sheaves have the meanings of the etale
and pro-etale sheaf conventions.
