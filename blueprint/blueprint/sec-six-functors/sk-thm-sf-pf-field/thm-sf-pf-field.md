+++
id = "thm-sf-pf-field"
kind = "theorem"
title = "Rational and algebraically closed stages"
order = 2098
uses = ["def-sf-datum", "def-sf-pf", "def-weil-algebraically-closed-coefficients", "def-weil-rationalization-karoubi", "thm-sf-pf-adic"]
+++
In the setting of [def-sf-datum], let $K,L$ be obtained by
rationalization from $\mathcal O_E$-objects, or represented at a finite
stage $E'/\mathbf Q_\ell$. Then $\operatorname{PF}_{f,K,L}$ is an
isomorphism over $E$ and over $\overline{\mathbf Q}_\ell$, compatible with
the extension functors and with finite reduction.

## Proof

The projection transformation is that of [def-sf-pf]; rationalization
is [def-weil-rationalization-karoubi].
The rationalization functor $-\otimes^L_{\mathcal O_E}E$ is exact,
commutes with $Rf_!$, $-\otimes^L$ and $Lf^*$, and carries the
mate-theoretic projection transformation to the mate-theoretic projection
transformation (the units and counits are transported, being those of the
axioms); an exact functor carries isomorphisms to isomorphisms, so
[thm-sf-pf-adic] gives the $E$-statement. For
$\overline{\mathbf Q}_\ell$, each object is represented over a finite stage
$E'/\mathbf Q_\ell$ by [def-weil-algebraically-closed-coefficients],
the $E'$-statement is the previous paragraph, and compatibility with
scalar extension makes the finite-stage system descend to the
$2$-colimit.
