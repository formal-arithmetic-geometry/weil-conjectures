+++
id = "lem-sc-genus-invariant"
kind = "lemma"
title = "The genus is invariant under extension"
order = 1030
uses = ["def-sc-curves", "def-sc-genus", "def-sc-jacobian", "lem-sc-flat-base-change-coherent", "thm-sc-jacobian-representability"]
+++
Let $C$ be a proper smooth connected curve over
$k$ and let $k\subseteq k'$ be algebraically closed. Then

$$
g(C_{k'})=g(C),
$$

compatibly with the Jacobian of
[thm-sc-jacobian-representability] (i.e. $J_{C_{k'}}\cong(J_C)_{k'}$, and the identifications of
[def-sc-jacobian] are compatible with base change).

## Proof

By definition ([def-sc-genus]),
$g(C)=\dim_kH^1(C,\mathcal O_C)$, and by
[lem-sc-flat-base-change-coherent] applied to
$\mathcal F=\mathcal O_C$ and the flat extension $k\to k'$,

$$
\dim_{k'}H^1(C_{k'},\mathcal O_{C_{k'}})=\dim_kH^1(C,\mathcal O_C),
$$

i.e. $g(C_{k'})=g(C)$. The Jacobian compatibility is the
base-change statement of [thm-sc-jacobian-representability].
