+++
id = "lem-kun-fibre-product-limits"
kind = "lemma"
title = "Fibre products commute with inverse limits"
order = 1660
+++
Let $(X_i\to S_i\leftarrow Y_i)_{i\in I}$ be a compatible inverse
system of schemes, and suppose all indicated inverse limits exist.
Then the canonical map

$$
\varprojlim_i(X_i\times_{S_i}Y_i)\longrightarrow
\bigl(\varprojlim_iX_i\bigr)\times_{\varprojlim_iS_i}
\bigl(\varprojlim_iY_i\bigr)
$$

is an isomorphism.

## Proof

Both sides represent the functor which sends a scheme $Z$ to the set
of compatible systems $(x_i,y_i,s_i)$ of maps $x_i:Z\to X_i$,
$y_i:Z\to Y_i$, $s_i:Z\to S_i$ with $s_i=x_i\circ\gamma_i$ and
$s_i=y_i\circ\delta_i$ (for the structural maps $\gamma_i,\delta_i$),
the left side through the universal property of the limit and of the
fibre product, the right side through the same two properties applied
in the other order; the two sets of cones correspond naturally, which
is the assertion.
