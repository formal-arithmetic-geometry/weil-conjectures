+++
id = "def-weil-pbc-four-arrows"
kind = "definition"
title = "Four finite-level arrows"
order = 1343
uses = ["def-weil-pbc-ambient-ringed-exchange", "def-weil-pbc-four-corners", "def-weil-pbc-projection-formula-map"]
+++
Let
$$
 h_n:A_n\xrightarrow{\sim}B_n,
 \qquad h'_n:C_n\xrightarrow{\sim}D_n
$$
be the isomorphisms supplied by the projection-formula maps on the corners
of the four-corners construction [def-weil-pbc-four-corners]. Let
$$
 v_n:A_n\to C_n
$$
be the tensor reduction of the ambient ringed exchange map
$$
 \Ex^A_{\square,K}:Lg^*Rf_*K\longrightarrow Rf'_*Lg'^*K
$$
of [def-weil-pbc-ambient-ringed-exchange], transported through the canonical
isomorphism
$Lg_n^*((Rf_*K)\otimes_A^LP_n)\simeq(Lg^*Rf_*K)\otimes_A^LP_n$. Let
$$
 v'_n:B_n\xrightarrow{\sim}D_n
$$
be the finite-level pro-etale exchange isomorphism for $K_n$, obtained from
its specified finite-coefficient etale-origin witness.

*Source:* the four arrows are Stacks entries. The exchange morphisms are the
canonical base change map $Lg^*Rf_*K\to Rf'_*L(g')^*K$ of Cohomology on
Sites, Remark 21.19.3 ([Tag
07A7](https://stacks.math.columbia.edu/tag/07A7)), constructed there in full
generality for a commutative diagram of ringed topoi as the adjoint of
$L(g')^*$ of the adjunction map $Lf^*Rf_*K\to K$; $v_n$ is its tensor
reduction along $P_n$, and $v'_n$ is its finite-level form, an isomorphism
by Theorem 61.30.1 ([Tag 09C9](https://stacks.math.columbia.edu/tag/09C9))
applied to $K_n$ with its etale-origin witness. The projection-formula
companions $h_n,h'_n$ are the map of Equation 21.50.0.1 ([Tag
0B56](https://stacks.math.columbia.edu/tag/0B56)) and its
perfect-coefficient form, Lemma 21.50.1 ([Tag
0944](https://stacks.math.columbia.edu/tag/0944)). Difference of generality:
Stacks' base change map is stated for ringed topoi with no completeness
hypothesis and no coefficient tower, and is not asserted to be an
isomorphism — the isomorphism is Stacks' proper base change theorem 61.30.1,
which states no construction of the map; the required identification of
$v'_n$ with the finite-level form of the specified etale-origin witness, and
the assembly of the two exchange arrows with their two projection-formula
companions on the corners of one square, are the blueprint's presentation at
the finite coefficient rings $P_n=A/I^n$.
