+++
id = "lem-cbc-proetale-extension-zero-base-change"
kind = "lemma"
title = "Pro-etale extension-by-zero base change"
order = 1583
uses = ["def-cbc-open-immersion-square", "def-weil-pbc-inverse-image", "lem-cbc-proetale-extension-zero"]
+++
Let

$$
\begin{array}{ccc}
U'&\xrightarrow{g_U}&U\\
j'\downarrow&&\downarrow j\\
X'&\xrightarrow{g}&X
\end{array}
$$

be an open-immersion square
and let $\Lambda$ be a finite commutative ring. For every complex
$K$ of $\Lambda$-module sheaves on $U_{\Proet}$ the canonical map

$$
g^{-1}j_!K\xrightarrow{\ \sim\ }j'_!g_U^{-1}K
$$

is an isomorphism, natural in $K$; here all functors are the
pro-etale ones of [lem-cbc-proetale-extension-zero].

## Proof

Both sides are left adjoints, and we identify their right adjoints.
By [lem-cbc-proetale-extension-zero] the functor $j_!$ is left
adjoint to $j^{-1}$ and is exact, and by
[def-weil-pbc-inverse-image] the same adjunction is available on
the primed square. For a complex $M$ on $X'_{\Proet}$ the two
Hom-functors in $K$ are therefore

$$
\operatorname{Hom}\bigl(g^{-1}j_!K,M\bigr)
\cong\operatorname{Hom}\bigl(j_!K,g_*M\bigr)
\cong\operatorname{Hom}\bigl(K,j^{-1}g_*M\bigr),
$$

$$
\operatorname{Hom}\bigl(j'_!g_U^{-1}K,M\bigr)
\cong\operatorname{Hom}\bigl(g_U^{-1}K,j'^{-1}M\bigr)
\cong\operatorname{Hom}\bigl(K,g_{U*}j'^{-1}M\bigr).
$$

The two right adjoints agree. For $V\to U$ the under-category of
$X$-objects under $V$ has $V$ itself as initial object, so the
value of $j^{-1}g_*M$ at $V$ is $M(V\times_XX')$; and the value
of $g_{U*}j'^{-1}M$ at $V$ is $j'^{-1}M(V\times_UU')= M(V\times_XX')$, the open-immersion square of
[def-cbc-open-immersion-square] being cartesian and $V\times_UU'$
being the same weakly etale $X'$-object as $V\times_XX'$. Both
identifications are restriction of sections along an open immersion,
so the two right adjoints are equal, not merely isomorphic. The two
Hom-functors in $K$ are therefore isomorphic, and by Yoneda the two
left adjoints are canonically isomorphic. The isomorphism is natural
in $K$, being induced by the naturality of the adjunction
isomorphisms, and it is the canonical map of the statement because
both sides of the comparison are assembled from the units and counits
of the displayed adjunctions.
