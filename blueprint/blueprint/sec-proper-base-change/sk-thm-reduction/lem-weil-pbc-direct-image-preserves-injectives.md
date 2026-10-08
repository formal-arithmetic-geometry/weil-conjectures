+++
id = "lem-weil-pbc-direct-image-preserves-injectives"
kind = "lemma"
title = "Direct image preserves injectives"
order = 1185
uses = ["def-weil-pbc-direct-image", "def-weil-pbc-inverse-image", "lem-sp-right-adjoint-preserves-injectives"]
+++
For every morphism $u:U\to V$, the functor $u_*$ sends injective etale sheaves
to injective etale sheaves. The relevant adjunction is $u^{-1}\dashv u_*$, and
$u^{-1}$ is exact.

## Proof

By the elementary criterion for injective objects ([lem-sp-right-adjoint-preserves-injectives]), a right adjoint to an exact
functor preserves injectives; the exact functor is $u^{-1}$ and the right
adjoint is $u_*$.
