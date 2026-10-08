+++
id = "lem-weil-pbc-finite-level-rectangle"
kind = "lemma"
title = "Finite-level exchange rectangle"
order = 1344
uses = ["def-weil-pbc-four-arrows", "def-weil-pbc-four-corners", "lemma-weil-pbc-perfect-projection-formula"]
+++
For every $n$, the diagram
$$
 \begin{array}{ccc}
  A_n&\xrightarrow{h_n}&B_n\\
  v_n\downarrow&&\downarrow v'_n\\
  C_n&\xrightarrow{h'_n}&D_n
 \end{array}
$$
commutes. Equivalently, $v'_nh_n=h'_nv_n$.

*Source:* the commutativity is Stacks Project, Cohomology on Sites, Remark
21.50.2 ([Tag 0E48](https://stacks.math.columbia.edu/tag/0E48)): the
projection-formula map (21.50.0.1, [Tag
0B56](https://stacks.math.columbia.edu/tag/0B56)) is compatible with the
base change map of Remark 21.19.3 ([Tag
07A7](https://stacks.math.columbia.edu/tag/07A7)), i.e. for a commutative
diagram of ringed topoi and $E\in D(\mathcal O_{\mathcal C})$,
$K\in D(\mathcal O_{\mathcal D})$ the square formed by
$Lg^*(Rf_*E\otimes^LK)\to Lg^*Rf_*(E\otimes^LLf^*K)$ (projection formula),
$Lg^*(Rf_*E\otimes^LK)\to Lg^*Rf_*E\otimes^LLg^*K$ (base change),
$Rf'_*L(g')^*E\otimes^LLg^*K\to Rf'_*(L(g')^*E\otimes^LL(f')^*Lg^*K)$
(projection formula) and
$Lg^*Rf_*(E\otimes^LLf^*K)\to Rf'_*L(g')^*(E\otimes^LLf^*K)$ (base change)
commutes; this is exactly the rectangle $v'_nh_n=h'_nv_n$ at the level of
the four corners of [def-weil-pbc-four-corners]. Difference of generality:
Stacks states the commutativity for arbitrary $E,K$ over ringed topoi, with
no completeness hypothesis, no coefficient tower and no finite coefficient
ring, and omits the verification ("we omit the verification"); the rectangle
is the finite-level instance at the perfect coefficient $P_n=A/I^n$ of the
adic coefficient datum, and it is this finite-level form that the completed
exchange below reduces to.

## Proof

The two routes around the rectangle are both the level-$n$ reduction of the
base-change mate, computed through the projection-formula isomorphisms on
the two sides; naturality of the perfect-coefficient projection-formula map
with respect to the base-change mate makes them equal, with the arrows of
[def-weil-pbc-four-arrows].
