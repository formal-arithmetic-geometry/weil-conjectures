+++
id = "lem-weil-pbc-clopen-section-direct-image"
kind = "lemma"
title = "Direct image from an open and closed section"
order = 1480
uses = ["def-weil-pbc-derived-categories", "def-weil-pbc-direct-image", "def-weil-pbc-extension-by-zero", "def-weil-pbc-scheme-conventions", "prop-weil-pbc-kinjective-resolutions-exist"]
+++
Let $p:V\to X$ be a scheme morphism and
$s:X\hookrightarrow V$ an
open immersion with
closed image and $p s=\operatorname{id}_X$.
For a finite ring $\Lambda$ and
$K\in\hyperref[def-weil-pbc-derived-categories]{D^+(X_{\Et},\Lambda)}$,
restriction to this component gives a canonical isomorphism

$$
Rp_*s_!K\xrightarrow{\sim}K,
$$

where $Rp_*$ and $s_!$ are the
derived direct image and
extension by zero.

## Proof

The disjoint open cover
$V=s(X)\amalg(V\setminus s(X))$ identifies sheaves on $V_{\Et}$
with pairs of sheaves on its components, by the sheaf gluing axiom.
In this product description the functor $s_!$ of
[def-weil-pbc-extension-by-zero] is $F\mapsto(F,0)$.
It is also right adjoint to the exact restriction to the first
component, and hence preserves injectives. For every etale $W\to X$,
the direct image in [def-weil-pbc-direct-image] has

$$
(p_*s_!F)(W)
=\Gamma(V\times_XW,s_!F)
=\Gamma(W,F),
$$

because $p s=\operatorname{id}_X$ and the other component contributes
zero. Apply this identity to a bounded-below injective resolution
from [prop-weil-pbc-kinjective-resolutions-exist]; its extension
by zero is still an injective resolution. The identity in each
degree is the asserted derived isomorphism.
