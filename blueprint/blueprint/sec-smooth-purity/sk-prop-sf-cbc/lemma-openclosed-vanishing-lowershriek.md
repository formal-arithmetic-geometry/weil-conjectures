+++
id = "lemma-openclosed-vanishing-lowershriek"
kind = "lemma"
title = "$i^*j_!$ vanishes"
order = 1536
lean = ["AlgebraicGeometry.Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range"]
uses = ["lemma-openclosed-vanishing-lowerstar"]
+++
In the situation of [lemma-openclosed-vanishing-lowerstar],
$i^*j_!\mathcal G=0$ for every $\mathcal G\in\shv{\et U}$.

## Proof

The point of the argument is that no section of $j_!\mathcal G$ is computed:
$j_!$ is a sheafification and its sections are not accessible. Instead one
uses only adjunctions. For every $\mathcal H\in\shv{\et Z}$,

$$
\Hom(i^*j_!\mathcal G,\mathcal H)
\cong\Hom(j_!\mathcal G,i_*\mathcal H)
\cong\Hom(\mathcal G,j^*i_*\mathcal H)=0
$$

by [lemma-openclosed-vanishing-lowerstar]. Taking
$\mathcal H=i^*j_!\mathcal G$ shows that the identity of
$i^*j_!\mathcal G$ is zero, that is, $i^*j_!\mathcal G=0$.
