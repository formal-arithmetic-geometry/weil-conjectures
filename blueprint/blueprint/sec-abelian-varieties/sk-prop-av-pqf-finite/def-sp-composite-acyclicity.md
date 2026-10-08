+++
id = "def-sp-composite-acyclicity"
kind = "definition"
title = "Composable pairs with an acyclicity condition"
order = 523
uses = ["def-sp-acyclic", "def-sp-grothendieck-abelian", "def-sp-injective-resolutions", "def-sp-left-exact-additive"]
+++
A *composable pair* $(F,G)$ consists of left exact additive
[def-sp-left-exact-additive] functors

$$
 \mathcal A\xrightarrow{\ F\ }\mathcal B\xrightarrow{\ G\ }\mathcal C
$$

between Grothendieck abelian categories
[def-sp-grothendieck-abelian]. $F$ *sends injectives to $G$-acyclics* if
$F(I)$ is $G$-acyclic [def-sp-acyclic] for every injective
[def-sp-injective-resolutions] object $I\in\mathcal A$.
