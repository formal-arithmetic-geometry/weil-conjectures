+++
id = "def-weil-karoubi-envelope"
kind = "definition"
title = "Karoubi envelope"
order = 1206
+++
For an additive category $\mathcal T$, the *Karoubi envelope*
$\Kar(\mathcal T)$ has objects $(K,e)$, where $K\in\mathcal T$ and
$e\in\operatorname{End}_{\mathcal T}(K)$ satisfies $e^2=e$, and morphisms
$u:(K,e)\to(L,d)$ the morphisms $u\in\Hom_{\mathcal T}(K,L)$ satisfying
$u=d\,u\,e$. The identity of $(K,e)$ is $e$, and composition is inherited
from $\mathcal T$. The canonical functor

$$
 \mathcal T\longrightarrow\Kar(\mathcal T),\qquad
 K\longmapsto(K,\operatorname{id}_K),\qquad f\longmapsto f,
$$

is the *inclusion of $\mathcal T$ in its Karoubi envelope*.

*Difference:* Stacks states neither the construction of the Karoubi envelope
nor its inclusion functor, and its splitting criterion is one of three
equivalent characterizations of Karoubianity rather than a construction
applied to a given category; the request on that section page to add the
construction of the Karoubi envelope stands as an open comment (Comment
5787), and the addition of the explicit section--retraction form of an
idempotent to Lemma 12.4.2 was declined.
