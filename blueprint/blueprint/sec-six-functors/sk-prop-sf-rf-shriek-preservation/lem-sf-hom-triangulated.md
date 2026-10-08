+++
id = "lem-sf-hom-triangulated"
kind = "lemma"
title = "Exactness of the internal Hom in each variable"
order = 2081
uses = ["def-weil-derived-pullback-tensor-hom", "def-weil-pbc-etale-site", "def-weil-pbc-kinjective-resolutions", "prop-weil-pbc-kinjective-resolutions-exist"]
+++
Let $A$ be a commutative ring, let $X$ be a scheme and let
$K',K,K'',M,M',M''$ be complexes of $A$-modules on $X_{\Et}$. If
$K'\to K\to K''\to K'[1]$ and $M'\to M\to M''\to M'[1]$ are
distinguished triangles of $D(X_{\Et},A)$, then the sequences

$$
R\mathcal Hom_A(K'',M)\to R\mathcal Hom_A(K,M)\to R\mathcal Hom_A(K',M)
\to R\mathcal Hom_A(K'',M)[1],
$$

$$
R\mathcal Hom_A(K,M')\to R\mathcal Hom_A(K,M)\to R\mathcal Hom_A(K,M'')
\to R\mathcal Hom_A(K,M')[1]
$$

are distinguished triangles, the internal Hom being that of
[def-weil-derived-pullback-tensor-hom], computed by a K-injective
resolution of the second variable.

## Proof

Choose a K-injective resolution $I\to M$, which exists by
[prop-weil-pbc-kinjective-resolutions-exist] and
[def-weil-pbc-kinjective-resolutions]. By
[def-weil-derived-pullback-tensor-hom] the object
$R\mathcal Hom_A(K,M)$ is represented by the Hom-complex
$\mathcal Hom^\bullet_A(K,I)$, and represent the first variable by a
complex of the same name. The Hom-complex of complexes of modules is
triangulated in each variable: the standard termwise identity
$\operatorname{Hom}^\bullet(\operatorname{Cone}(u),I)\cong \operatorname{Cone}(\operatorname{Hom}^\bullet(u,I))[-1]$ exhibits the
first sequence as a triangle, and the identity
$\operatorname{Hom}^\bullet(K,\operatorname{Cone}(v))\cong \operatorname{Cone}(\operatorname{Hom}^\bullet(K,v))$, valid because a
complex of injectives is degreewise injective, exhibits the second. This
is the basic homological algebra of the Hom-complex, and it applies to the
sheaves of [def-weil-pbc-etale-site] termwise because the Hom-complex
is formed degreewise in the abelian category of module sheaves.
