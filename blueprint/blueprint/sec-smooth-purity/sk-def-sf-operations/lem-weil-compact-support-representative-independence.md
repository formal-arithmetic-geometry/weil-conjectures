+++
id = "lem-weil-compact-support-representative-independence"
kind = "lemma"
title = "Independence of the integral representative"
order = 1494
uses = ["def-compact-support-direct-image-detailed", "def-weil-derived-complete-integral-detailed", "def-weil-derived-limit", "def-weil-integral-rational-qbar-compact-support", "def-weil-rationalization-karoubi", "def-weil-scheme-morphism-properties", "lem-compact-support-direct-image-triangulated", "prop-weil-pbc-rational-transport"]
+++
Let $K_0$ be a field, let $X,Y$ be finite-type
[def-weil-scheme-morphism-properties] $K_0$-schemes, let $f:X\to Y$ be a
separated finite-type $K_0$-morphism, fix a prime $\ell$ whose image in $K_0$
is invertible, and choose a finite extension $E/\Ql$ with valuation ring
$\mathcal O_E$ and uniformizer $\varpi_E$. Let $K,K'\in D^b_c(X,\mathcal
O_E)$ be integral complexes of the derived-complete integral category
[def-weil-derived-complete-integral-detailed] representing the same object of
the rationalized category $D^b_c(X,E)$ of
[def-weil-rationalization-karoubi]. Then the two objects

$$
 (Rf_!K)\otimes^L_{\mathcal O_E}E,\qquad
 (Rf_!K')\otimes^L_{\mathcal O_E}E
$$

of $D^b_c(Y,E)$, formed from the compact-support direct image
[def-weil-integral-rational-qbar-compact-support], are canonically
isomorphic.

## Proof

The integral compact-support functor $K\mapsto
R\varprojlim_n\operatorname{Res}_nRf_{!,n}K_n$ of
[def-weil-integral-rational-qbar-compact-support] is $\mathcal O_E$-linear
and exact on the derived-complete integral constructible category
$D^b_c(X,\mathcal O_E)$ of [def-weil-derived-complete-integral-detailed]: it
is built from the finite-level functors $Rf_{!,n}$ of
[def-compact-support-direct-image-detailed], each triangulated by
[lem-compact-support-direct-image-triangulated], and from the derived limit
[def-weil-derived-limit], which is triangulated by its defining triangle. By
the rational-transport proposition of the proper-base-change chapter every
exact $\mathcal O_E$-linear functor on the integral constructible category
extends uniquely to its rationalization $D^b_c(X,E)$ of
[def-weil-rationalization-karoubi]; a uniquely determined extension takes the
same value on any two integral representatives $K,K'$ of one object, and that
identification is the canonical isomorphism asserted.
