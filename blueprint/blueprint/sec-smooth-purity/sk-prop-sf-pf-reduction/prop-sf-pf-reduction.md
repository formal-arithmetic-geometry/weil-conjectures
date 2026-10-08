+++
id = "prop-sf-pf-reduction"
kind = "theorem"
title = "Compatibility with finite reduction"
order = 1885
tags = ["latex:proposition"]
uses = ["def-sf-datum", "def-sf-pf", "lem-fix-compact-support-coefficient-change", "lem-fix-operation-reduction", "thm-sf-pf-finite"]
+++
In the setting of [def-sf-datum], let $m\le n$ and let
$K\in D^b_{ctf}(X,A_{E,n})$, $L\in D^b_{ctf}(Y,A_{E,n})$ with reductions
$K_m,L_m$. Then the square comparing $\operatorname{PF}_{f,K,L}$ and
$\operatorname{PF}_{f,K_m,L_m}$ through the finite-reduction
compatibilities of $Rf_!$, $-\otimes^L$ and $Lf^*$ commutes; hence
$\operatorname{PF}_{f,K,L}$ is an isomorphism if and only if
$\operatorname{PF}_{f,K_m,L_m}$ is.

## Proof

Use the pullback and tensor comparisons of
[lem-fix-operation-reduction] and the compact-support comparison
of [lem-fix-compact-support-coefficient-change]. Transpose both
routes around the reduction square for the projection transformation
of [def-sf-pf]. Each route pulls back the first factor, applies
the counit, and tensors with the reductions of the remaining factors.
Associativity of derived tensor and compatibility of that counit
with coefficient change identify these composites. Thus the square
commutes as a square of the specified maps. This argument does not
infer equality of morphisms merely from equality on geometric stalks.
Both horizontal maps are isomorphisms by [thm-sf-pf-finite];
in particular the asserted equivalence of invertibility holds.
