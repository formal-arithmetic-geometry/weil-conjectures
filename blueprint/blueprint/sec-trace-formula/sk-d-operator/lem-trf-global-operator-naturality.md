+++
id = "lem-trf-global-operator-naturality"
kind = "lemma"
title = "Naturality of the global operator"
order = 2291
uses = ["def-trf-admissibility", "def-trf-coefficient-conventions", "def-trf-correspondence", "def-trf-global-operator"]
+++
Fix the coefficient
conventions and an
admissible cohomological
correspondence $c=(c_1,c_2):C\to X\times_sX$ whose ordinary leg
$c_2$ is proper, and let $K\in D^b_{ctf}(X,A)$. Then the global
operator $T_c(u)$ of [def-trf-global-operator] is natural in
the pair $(u,K)$: a morphism of correspondences
$u\to u'$ over a morphism $K\to K'$ in $D^b_{ctf}(X,A)$ induces
a commutative square relating $T_c(u)$ and $T_c(u')$.

## Proof

By [def-trf-global-operator] the operator $T_c(u)$ is the
composite of the five arrows displayed there. Each of them is
natural in $u$ and $K$: the unit of the adjunction
$Lc_2^*\dashv Rc_{2*}$ and the counit of the adjunction
$Rc_{1!}\dashv Rc_1^!$ of [def-trf-admissibility] are natural
transformations, the two comparison isomorphisms are the specified
structure isomorphisms of the six-operations package and are natural
in the coefficient object, and $R\Gamma_c(C,-)$ is a functor, so
that $R\Gamma_c(C,u)$ is natural in $u$ and in $K$ by
[def-trf-coefficient-conventions]. A composite of natural
arrows is natural, which is the displayed commutativity.
