+++
id = "fix-prop-projection-formula"
kind = "theorem"
title = "Compact-support projection formula at all coefficient stages"
order = 2109
tags = ["latex:proposition"]
uses = ["def-compact-support-direct-image-detailed", "def-exchange-projection", "def-fix-six-functor-datum", "def-weil-derived-direct-image", "def-weil-derived-pullback-tensor-hom", "def-weil-finite-tor-amplitude", "def-weil-scheme-morphism-properties", "def-wf-tensor-product", "lem-fix-weil-operations", "lem-weil-finite-compact-projection-formula", "prop-sf-pf-coherence", "prop-sf-pf-reduction", "thm-sf-pf-adic", "thm-sf-pf-field", "thm-sf-pf-proetale", "thm-sf-comp-composition"]
+++
In the six-functor datum of
[def-fix-six-functor-datum], let $f:X\to Y$ be
separated of finite
type, let $K\in D^b_c(X,\Lambda)$ and
$L\in D^b_{ctf}(Y,\Lambda)$, using the
finite-Tor subcategory.
The
projection transformation, built from the
derived tensor and pullback
and the compact-support direct image of
[def-compact-support-direct-image-detailed],
is then an isomorphism at every coefficient stage:

$$
\operatorname{PF}_{f,K,L}:Rf_!K\otimes^L_{\Lambda}L
\xrightarrow{\ \sim\ }Rf_!\bigl(K\otimes^L_{\Lambda}Lf^*L\bigr),
$$

natural in $K$ and $L$, compatible with the composition law of
[thm-sf-comp-composition] (associativity pentagon), with the compactification comparisons, with
finite reduction on the stated finite-Tor domains and scalar extension,
and with the identification
$Rf_!\cong Rf_*$ for proper $f$; at the rational and algebraically
closed stages the isomorphism restricts to the Weil categories of
[def-wf-tensor-product]. A projection formula for the
derived direct image is asserted
only in the proper case, where it is this same statement via
$Rf_!\cong Rf_*$.

## Proof

The geometric-fiber argument of
[lem-weil-finite-compact-projection-formula] proves the finite
coefficient formula. The compatibility of the specified maps under
successive coefficient reductions is [prop-sf-pf-reduction].
Thus [thm-sf-pf-adic] reconstructs the integral map, and
[thm-sf-pf-field] transports it to the field stages.
The site comparison of [thm-sf-pf-proetale] gives the stated
pro-etale realization. The composition, refinement, exchange and
proper-coincidence identities are [prop-sf-pf-coherence].
Its equivariance for Weil complexes is the equivariance of the
projection transformation in [lem-fix-weil-operations].
Every step constructs or compares the same projection map; none
uses smooth purity or Verdier duality.
