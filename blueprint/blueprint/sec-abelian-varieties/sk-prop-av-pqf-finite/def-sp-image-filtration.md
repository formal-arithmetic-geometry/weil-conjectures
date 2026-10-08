+++
id = "def-sp-image-filtration"
kind = "definition"
title = "Image filtrations"
order = 508
uses = ["def-sp-abelian", "def-sp-filtration"]
+++
Let $(A,F)$ be a filtered object [def-sp-filtration] and let $A\to B$ be a
morphism in the abelian category [def-sp-abelian] $\mathcal A$. The *image
filtration* on $B$ is the filtration

$$
 F^nB:=\operatorname{im}\bigl(F^nA\to B\bigr).
$$

(*Stacks Project:* the case of this construction used below is the induced
filtration on the homology of a filtered differential object, Definition
12.23.4, Tag [012E](https://stacks.math.columbia.edu/tag/012E)
($F^pH(K,d)=\operatorname{im}(H(F^pK,d)\to H(K,d))$); the definition above is
the same recipe for an arbitrary morphism $A\to B$.)
