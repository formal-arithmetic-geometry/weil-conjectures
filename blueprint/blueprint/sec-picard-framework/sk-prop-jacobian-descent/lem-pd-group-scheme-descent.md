+++
id = "lem-pd-group-scheme-descent"
kind = "lemma"
title = "The descended scheme is a group scheme"
order = 866
uses = ["def-pc-base-change", "def-pd-descent-datum", "def-sc-group-scheme", "lem-pd-morphisms-descend"]
+++
Let $k\subseteq K$ be a finite separable field extension, let $J_K$ be a scheme
over $K$ with a descent datum over
$\Spec(K)/\Spec(k)$ which is effective with descended scheme $J$, and suppose
that $J_K$ carries a $K$-group scheme structure
whose multiplication, unit and inverse are compatible with the descent datum.
Then $J$ carries a unique $k$-group scheme structure whose
base change to $K$ is the given one.

## Proof

A group scheme structure on $J_K$ over $K$ is a triple of morphisms
$m_K:J_K\times_KJ_K\to J_K$, $e_K:\Spec(K)\to J_K$ and
$i_K:J_K\to J_K$ satisfying the group axioms, which are equalities between
morphisms built from $m_K,e_K,i_K$ by composition and projection; this is the
$K$-group scheme structure of [def-sc-group-scheme], and all fibre
products below are the base changes of [def-pc-base-change]. Base
change to $K$ commutes with fibre products, so
$(J\times_kJ)\times_kK=J_K\times_KJ_K$, and the
[def-pd-descent-datum] on $J_K$ induces
one on $J_K\times_KJ_K$; the morphism $m_K$ is compatible with these data
because the descent datum was constructed from the functor
$\operatorname{Pic}^0_{C/k}$ and the group law on the functor is defined over
$k$. Applying [lem-pd-morphisms-descend] to $m_K$, to $e_K$ and to
$i_K$ produces morphisms $m,e,i$ over $k$; the group axioms for $m,e,i$
follow from those for $m_K,e_K,i_K$ because base change along the faithfully
flat morphism $\Spec(K)\to\Spec(k)$ is injective on morphisms, and the
resulting structure is a $k$-group scheme structure in the sense of
[def-sc-group-scheme]. Uniqueness follows from the same injectivity.
