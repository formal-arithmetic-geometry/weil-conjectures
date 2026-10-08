+++
id = "lem-weil-qbar-idempotent-complete"
kind = "lemma"
title = "Idempotent completeness of the common-stage category"
order = 2115
uses = ["def-weil-algebraically-closed-coefficients", "def-weil-finite-field-fiber", "def-weil-karoubi-envelope", "def-weil-rationalization-karoubi", "prop-weil-filtered-retract-descent", "thm-weil-pbc-finite-stage-karoubian"]
+++
Fix the global finite-field datum [def-weil-finite-field-fiber], a prime
$\ell\neq p$, a scheme $Y$, and an algebraic closure $\Qlb$ of $\Ql$, and let
$\mathcal C_Y=D^b_c(Y,\Qlb)$ be the common-stage coefficient category of
[def-weil-algebraically-closed-coefficients], whose finite stages are the
rationalized categories $D^b_c(Y,E)$ of
[def-weil-rationalization-karoubi]. Then $\mathcal C_Y$ is idempotent
complete, and the canonical functor

$$
 \mathcal C_Y\longrightarrow\Kar(\mathcal C_Y)
$$

into its Karoubi envelope is an exact equivalence.

## Proof

Every finite stage $D^b_c(Y,E)$ of [def-weil-rationalization-karoubi] is
idempotent complete by the finite-stage Karoubian theorem of the
proper-base-change chapter. The category $\mathcal C_Y$ of
[def-weil-algebraically-closed-coefficients] is the common-stage category of
the filtered system of these stages, so the filtered retract-descent
proposition applies: every idempotent of the common-stage category splits,
and a splitting may be represented over a single finite coefficient field.
The canonical functor into the Karoubi envelope is fully faithful by
definition of the envelope and essentially surjective because every
idempotent splits, hence it is an exact equivalence.
