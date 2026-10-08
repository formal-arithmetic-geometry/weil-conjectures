+++
id = "lem-weil-pbc-rectangle-derived-limit"
kind = "lemma"
title = "The rectangle passes to the derived limit"
order = 1346
uses = ["def-weil-pbc-derived-inverse-limit", "lem-weil-pbc-tower-compatibility", "prop-weil-pbc-rlim-functoriality"]
+++
Put
$$
 A_\infty=\Rlim A_\bullet,\quad
 B_\infty=\Rlim B_\bullet,\quad
 C_\infty=\Rlim C_\bullet,\quad
 D_\infty=\Rlim D_\bullet,
$$
and let $H,V,H',V'$ be the images under the triangulated functor $\Rlim$ ([prop-weil-pbc-rlim-functoriality]) of
the four compatible tower morphisms $h,v,h',v'$. Then
$$
 V'H=H'V:A_\infty\longrightarrow D_\infty.
$$
The $n$-th component of both sides is the equality $v'_nh_n=h'_nv_n$ at
level $n$.

*Source note:* the assertion is the functoriality of the derived limit of
Stacks Project, Derived Categories, Definition 13.34.1 ([Tag
08TC](https://stacks.math.columbia.edu/tag/08TC)), whose triangle is natural
in the system, so that a functorial model of $\Rlim$ carries compatible
tower morphisms to morphisms and preserves composition. The Stacks entry
states the triangle for one system; the blueprint adds the assembly over the
tower category, the functoriality of the sequential derived inverse limit
proved above, and the identification of the $n$-th components of both sides
with the finite-level equations $v'_nh_n=h'_nv_n$.

## Proof

The triangle functor $\Rlim$ of the derived inverse limit preserves the
rectangle commutation of [lem-weil-pbc-tower-compatibility], and evaluation
at $n$ recovers the finite-level equality.
