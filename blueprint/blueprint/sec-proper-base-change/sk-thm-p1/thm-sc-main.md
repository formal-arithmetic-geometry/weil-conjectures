+++
id = "thm-sc-main"
kind = "theorem"
title = "Smooth-curve calculations"
order = 1120
uses = ["def-sc-constant-sheaves", "def-sc-curves", "def-sc-field-extension", "def-weil-pbc-eight-curve-assertions", "lem-sc-c1", "lem-sc-c2", "lem-sc-c3", "lem-sc-c4", "lem-sc-c5", "lem-sc-c6", "lem-sc-c7", "lem-sc-c8", "thm-sc-affine-cohomology", "thm-sc-constant-invariance", "thm-sc-proper-cohomology"]
+++
Let $k$ be algebraically closed and let $C$ be a
smooth separated connected curve over $k$. Let
$\mathbf F_r$ be the constant sheaf
([def-sc-constant-sheaves]) and consider the assertions
$\mathcal C_1,\dots,\mathcal C_8$ of
[def-weil-pbc-eight-curve-assertions].

1. **(a)** If $r\neq\operatorname{char}k$, then
$\mathbf F_r$ satisfies $\mathcal C_1$, $\mathcal C_4$,
$\mathcal C_6$, and $\mathcal C_8$; it satisfies $\mathcal C_2$
when $C$ is affine and $\mathcal C_5,\mathcal C_7$ when $C$
is proper. Explicitly (for $r\neq\operatorname{char}k$):
$$
H^0(C,\mathbf F_r)=\mathbf Z/r\mathbf Z,\qquad
H^2(C,\mathbf F_r)=0\ \text{if}\ C\ \text{is affine},
$$
and, after choosing the trivialization by a primitive $r$-th
root of unity, there is a short exact sequence
$$
0\longrightarrow\mathcal O_C(C)^\times/\mathcal O_C(C)^\times{}^{\,r}
\longrightarrow H^1(C,\mathbf F_r)
\longrightarrow\operatorname{Pic}(C)[r]\longrightarrow0.
$$
If $C$ is proper of genus $g$,
$$
H^0(C,\mathbf F_r)=\mathbf Z/r\mathbf Z,\quad
H^1(C,\mathbf F_r)=(\mathbf Z/r\mathbf Z)^{2g},\quad
H^2(C,\mathbf F_r)=\mathbf Z/r\mathbf Z,\quad
H^q(C,\mathbf F_r)=0\ (q>2),
$$
and all these identifications are compatible with
algebraically closed field
extension (the pullback maps are isomorphisms).
1. **(b)** If $\operatorname{char}k=p>0$, the constant sheaf
$\mathbf F_p$ satisfies $\mathcal C_1$, $\mathcal C_3$, and
$\mathcal C_8$; it satisfies $\mathcal C_2$ when $C$ is affine
and $\mathcal C_5,\mathcal C_7$ when $C$ is proper.
1. **(c)** The maps in $\mathcal C_6$, $\mathcal C_7$, and
$\mathcal C_8$ are the pullback and restriction maps fixed in
[def-weil-pbc-eight-curve-assertions] (and in
[def-sc-field-extension]).

## Proof

Assertions (a) and (b) are the conjunctions, respectively, of
[lem-sc-c1], [lem-sc-c4], [lem-sc-c6],
[lem-sc-c8], [lem-sc-c2] (affine case) and
[lem-sc-c5], [lem-sc-c7] (proper case) for
$r\neq\operatorname{char}k$, and of [lem-sc-c1],
[lem-sc-c3], [lem-sc-c8], [lem-sc-c2] (affine) and
[lem-sc-c5], [lem-sc-c7] (proper) for
$r=\operatorname{char}k=p>0$, exactly as stated in
[def-weil-pbc-eight-curve-assertions]. The explicit
identifications are [thm-sc-proper-cohomology] and
[thm-sc-affine-cohomology], and the compatibility with field
extension is [thm-sc-constant-invariance]. Assertion (c) is by
the definitions of the maps in [def-weil-pbc-eight-curve-assertions]
(and [def-sc-field-extension]).
