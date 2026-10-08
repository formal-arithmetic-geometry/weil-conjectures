+++
id = "def-weil-pbc-four-corners"
kind = "definition"
title = "Four finite-level corners"
order = 1342
uses = ["def-weil-pbc-adic-coefficient-datum", "def-weil-pbc-cartesian-square", "def-weil-pbc-completed-pullback", "def-weil-pbc-proetale-operations"]
+++
Let $\square$ be cartesian [def-weil-pbc-cartesian-square] with $f$ proper,
let $K$ be derived $I$-complete in the sense of the adic coefficient datum,
put $K_n=K\otimes_A^LP_n$, and put
$$
 E=Lg'^*K,
 \qquad E_n=Lg_n'^*K_n
       \xleftarrow{\sim}E\otimes_A^LP_n.
$$
Define four objects of $D(Y'_{\Proet},P_n)$:
$$
 \begin{aligned}
  A_n&=Lg_n^*((Rf_*K)\otimes_A^LP_n),&
  B_n&=Lg_n^*Rf_*K_n,\\
  C_n&=(Rf'_*E)\otimes_A^LP_n,&
  D_n&=Rf'_*E_n.
 \end{aligned}
$$

*Source note:* no Stacks Project entry states this four-corner datum: its
inputs are given separately by the completed pullback and its finite
reduction (Lemma 61.20.2, [Tag
099N](https://stacks.math.columbia.edu/tag/099N)), the proper base-change
isomorphism (Theorem 61.30.1, [Tag
09C9](https://stacks.math.columbia.edu/tag/09C9)) and the projection formula
that identifies $A_n$ with $B_n$ and $C_n$ with $D_n$ after tensoring with
the perfect coefficient $P_n$ (Equation 21.50.0.1, [Tag
0B56](https://stacks.math.columbia.edu/tag/0B56), with Lemma 21.50.1, [Tag
0944](https://stacks.math.columbia.edu/tag/0944)), but no entry assembles
the four finite-level corners $A_n,B_n,C_n,D_n$ of one square; the blueprint
adds that assembly, at the finite coefficient rings $P_n=A/I^n$.
