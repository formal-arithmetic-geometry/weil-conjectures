+++
id = "lem-weil-rationalization-idempotent-complete"
kind = "lemma"
title = "Idempotent completeness of the rationalized category"
order = 2114
uses = ["def-weil-derived-complete-integral-detailed", "def-weil-karoubi-envelope", "def-weil-rationalization-karoubi", "thm-weil-karoubian-bounded-t", "thm-weil-pbc-finite-stage-karoubian"]
+++
Let $E/\Ql$ be a finite extension with valuation ring $\mathcal O_E$, let $Y$
be a scheme, and let $D^b_c(Y,E)$ be the rationalized category of
[def-weil-rationalization-karoubi]. Then $D^b_c(Y,E)$ is idempotent
complete, and the canonical functor

$$
 D^b_c(Y,E)\longrightarrow\Kar\bigl(D^b_c(Y,E)\bigr)
$$

into its Karoubi envelope is an exact equivalence.

## Proof

The rationalization $D^b_c(Y,E)$ of [def-weil-rationalization-karoubi] is the
scalar localization of the derived-complete integral category
$D^b_c(Y,\mathcal O_E)$ of [def-weil-derived-complete-integral-detailed] at
the central endomorphism given by $\varpi_E$, and it carries the rationalized
standard bounded $t$-structure, whose restriction to the integral category is
given by the levelwise truncations on the reduction tower. By the
finite-stage Karoubian theorem the rationalization of the integral
constructible category at a finite coefficient field is idempotent complete,
and the canonical functor into the Karoubi envelope is an exact equivalence.
The same conclusion follows from the bounded $t$-structure alone, every
idempotent of a triangulated category with a bounded $t$-structure splitting
by the Karoubian bounded-$t$ theorem. Both displayed assertions are therefore
established.
