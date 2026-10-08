+++
id = "lemma-weil-pbc-level-map-rectangle"
kind = "lemma"
title = "The finite-level exchange rectangle"
order = 1329
uses = ["def-weil-pbc-level-map-arrows", "lemma-weil-pbc-projection-formula-base-change-naturality"]
+++
For every $n$, the diagram

$$
\begin{CD}
A_n @>{h_n}>> B_n\\
@V{v_n}VV @VV{v'_n}V\\
C_n @>{h'_n}>> D_n
\end{CD}
$$

commutes; equivalently, its two composites satisfy

$$
v'_nh_n=h'_nv_n:A_n\longrightarrow D_n.
$$

## Proof

This is the base-change naturality rectangle for the projection-formula map
with coefficient $P_n$. To expose the equality, adjoint both composites to
$X'$. Their common adjoint is

$$
L(g')^*Lf^*Rf_*K\otimes^LP_n
\xrightarrow{L(g')^*(\epsilon_K)\otimes1}
L(g')^*K\otimes^LP_n=E_n.
$$

Thus every unit, counit, tensor associator, and Cartesian comparison occurs
in the same order in the two adjoints. Equality after adjunction proves the
displayed component equality.
