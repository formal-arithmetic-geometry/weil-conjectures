+++
id = "lem-weil-weil-complex-qbar-idempotent-complete"
kind = "lemma"
title = "Idempotent completeness of the common-stage Weil category"
order = 1887
uses = ["def-weil-algebraically-closed-coefficients", "def-weil-constructible-heart", "def-weil-finite-field-fiber", "def-weil-karoubi-envelope", "def-weil-weil-sheaf-complex", "prop-weil-filtered-retract-descent", "prop-weil-heart-abelian", "thm-weil-karoubian-bounded-t"]
+++
Fix the finite-field datum [def-weil-finite-field-fiber] $p,a,q,k_0,k$, a
prime $\ell\neq p$, a finite-type $k_0$-scheme $Y_0$ with
$Y=Y_0\times_{k_0}k$, and an algebraic closure $\Qlb$ of $\Ql$, and let
$D^b_{c,\mathrm W}(Y,\Qlb)$ be the common-stage Weil category of
[def-weil-weil-sheaf-complex]. Then $D^b_{c,\mathrm W}(Y,\Qlb)$ is idempotent
complete, and the canonical functor

$$
 D^b_{c,\mathrm W}(Y,\Qlb)\longrightarrow
 \Kar\bigl(D^b_{c,\mathrm W}(Y,\Qlb)\bigr)
$$

into its Karoubi envelope is an exact equivalence.

## Proof

At a finite coefficient field $E$, the category $D^b_{c,\mathrm W}(Y,E)$ of
[def-weil-weil-sheaf-complex] is the localization of bounded complexes of
constructible $E$-Weil sheaves at equivariant quasi-isomorphisms, and its
heart is the category of constructible $E$-Weil sheaves, which is abelian:
kernels and cokernels of morphisms of Weil sheaves are computed in the
constructible heart [def-weil-constructible-heart], and the Frobenius
isomorphism $\theta$ is carried along. The equivariant standard
$t$-structure is therefore bounded with abelian heart, so by the Karoubian
bounded-$t$ theorem every finite stage $D^b_{c,\mathrm W}(Y,E)$ is idempotent
complete and its canonical functor into the Karoubi envelope is an exact
equivalence. The category $D^b_{c,\mathrm W}(Y,\Qlb)$ is the 2-colimit of
these stages over the directed set of finite extensions of $\Ql$, as recorded
in the common-stage construction of
[def-weil-algebraically-closed-coefficients]; by the filtered retract-descent
proposition it is idempotent complete, an idempotent of the colimit
descending to a finite stage and splitting there, and its canonical functor
into the Karoubi envelope is again an exact equivalence.
