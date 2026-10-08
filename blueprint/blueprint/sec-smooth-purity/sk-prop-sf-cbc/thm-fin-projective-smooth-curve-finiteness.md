+++
id = "thm-fin-projective-smooth-curve-finiteness"
kind = "theorem"
title = "Constant-coefficient finiteness for projective smooth curves"
order = 1611
uses = ["cor-weil-pbc-geometric-fiber-finite", "def-pc-projective-morphism", "def-sbc-smooth-morphisms", "def-weil-pbc-constructible-complexes", "def-weil-pbc-direct-image", "def-weil-pbc-scheme-conventions", "fin4-lem-stalk-constructibility-criterion", "lem-fin-projective-curve-betti-cardinalities", "lem-pc-projective-proper"]
+++
Let $S$ be Noetherian
and let $f:X\to S$ be
projective and
smooth, with geometric fibres
of pure dimension one. If $\ell$ is a prime invertible on $S$,
every higher direct image
$R^rf_*\mathbf F_\ell$ is
constructible.

## Proof

The morphism is proper by [lem-pc-projective-proper].
Proper base change [cor-weil-pbc-geometric-fiber-finite]
identifies its stalks with $H^r(X_{\bar s},\mathbf F_\ell)$.
These stalks are finite and have constructible cardinalities by
[lem-fin-projective-curve-betti-cardinalities].
The fully proved criterion
[fin4-lem-stalk-constructibility-criterion] now applies to
the sheaf $R^rf_*\mathbf F_\ell$.
Proper base change was used only as an isomorphism; finiteness
of the fibre groups came from the curve calculation.
