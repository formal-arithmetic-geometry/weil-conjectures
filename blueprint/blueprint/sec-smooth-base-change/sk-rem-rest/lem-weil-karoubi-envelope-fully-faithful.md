+++
id = "lem-weil-karoubi-envelope-fully-faithful"
kind = "lemma"
title = "The inclusion of a category in its Karoubi envelope is fully faithful"
order = 1419
uses = ["def-weil-karoubi-envelope"]
+++
Let $\mathcal T$ be an additive category and let $\Kar(\mathcal T)$ be its
Karoubi envelope [def-weil-karoubi-envelope]. The canonical functor

$$
 \mathcal T\longrightarrow\Kar(\mathcal T),\qquad
 K\longmapsto(K,\operatorname{id}_K),\qquad f\longmapsto f,
$$

is fully faithful.

(*Source note:* no Stacks Project entry states this form: Stacks does not
construct the Karoubi envelope (Homological Algebra, Section 12.4, Tag
[09SF](https://stacks.math.columbia.edu/tag/09SF), states the Karoubian
property in Definition 12.4.1, Tag
[09SG](https://stacks.math.columbia.edu/tag/09SG), and characterizes it in
Lemma 12.4.2, Tag [09SH](https://stacks.math.columbia.edu/tag/09SH)), hence
states no full faithfulness for the inclusion of a category in its envelope;
the blueprint adds the elementary verification that the canonical functor is
bijective on morphism sets, which is what the bounded-t-structure argument
below uses to read an equivalence off full faithfulness.)

## Proof

By [def-weil-karoubi-envelope] the objects of $\Kar(\mathcal T)$ are the
pairs $(K,e)$ with $e^2=e$, the morphisms $(K,e)\to(L,d)$ are the morphisms
$u:K\to L$ of $\mathcal T$ satisfying $u=d\,u\,e$, and composition and
identities are those of $\mathcal T$. For $f:K\to L$ the condition is
$\operatorname{id}_L\,f\,\operatorname{id}_K=f$, which every morphism $f$
satisfies, so the map

$$
 \Hom_{\mathcal T}(K,L)\longrightarrow
 \Hom_{\Kar(\mathcal T)}\bigl((K,\operatorname{id}_K),
 (L,\operatorname{id}_L)\bigr),\qquad f\longmapsto f,
$$

is bijective; it is the identity on underlying morphisms, so it preserves
composition and identities. Hence the canonical functor is full and faithful.
