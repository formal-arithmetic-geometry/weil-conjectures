+++
id = "def-sf-datum"
kind = "definition"
title = "Six-functor datum, axiomatized"
order = 1498
+++
Fix the global finite-field datum
$(p,a,q,k_0,k)$ with $k=\overline{\mathbf F}_q$, a prime $\ell\ne p$, a
finite extension $E/\mathbf Q_\ell$ with valuation ring $\mathcal O_E$ and
uniformizer $\varpi_E$, an integer $n\ge1$, and put
$A_{E,n}=\mathcal O_E/\varpi_E^n$ and
$\Lambda\in\{A_{E,n},\mathcal O_E,E,\overline{\mathbf Q}_\ell\}$ as in
def:weil-derived-complete-integral,
def:weil-rationalization-karoubi,
def:weil-algebraically-closed-coefficients. A *six-functor
datum* is the datum of the
six-functor datum of [thm-weil-six-operations] —
the categories $D^b_{ctf}(X,\Lambda)$, the functors $Lf^*,Rf_*,Rf_!, Rf^!$, $-\otimes^L_\Lambda-$, $R\mathcal H om_\Lambda(-,-)$, the
exchange and projection
transformations, the compact-support
direct image $Rf_!=R\bar f_*j_!$ for a compactification, and the
exceptional inverse image
— subject to the following axioms, for all composable separated
finite-type morphisms and all $K,L$ in the stated finite-Tor domains:

1. ****(A1)**** $Lf^*\dashv Rf_*$ and $Rf_!\dashv Rf^!$, with the
pasted units and counits for composites;
1. ****(A2)**** base change: $Lg^*Rf_!\cong Rf'_!Lg'^*$ for every
Cartesian square, and $Lg^*Rf_*\cong Rf'_*Lg'^*$ for proper $f$ or smooth
$g$;
1. ****(A3)**** the projection transformation is an isomorphism
([def-sf-pf]);
1. ****(A4)**** the composition law $R(g\circ f)_!\cong Rg_!Rf_!$
with its pentagon, and $Rf_!\cong Rf_*$ for proper $f$;
1. ****(A5)**** compatibility of all of the above with finite
reduction, scalar extension, and the pro-étale realization;
1. ****(A6)**** the dualizing functor
$D_X=R\mathcal H om_X(-,\omega_X)$ is a contravariant exact anti-equivalence
of $D^b_{ctf}(X,\Lambda)$ with $K\to D_XD_XK$ an isomorphism (Verdier
biduality).

This is an axiomatized framework: a formal consequence may use only
the clauses explicitly invoked in its proof. For the concrete coefficient
system each clause needs its own verification on the stated domain; the
definition itself does not discharge those verification obligations.
