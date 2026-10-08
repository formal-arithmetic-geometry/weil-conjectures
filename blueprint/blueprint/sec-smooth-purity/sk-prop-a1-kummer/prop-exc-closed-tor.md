+++
id = "prop-exc-closed-tor"
kind = "theorem"
title = "Finite Tor amplitude for closed support"
order = 1913
tags = ["latex:proposition"]
uses = ["def-weil-finite-tor-amplitude", "def-weil-pbc-constructible-complexes", "def-weil-pbc-direct-image", "def-weil-pbc-scheme-conventions", "lem-exc-closed-ambient", "lem-exc-closed-amplitude", "lem-exc-closed-support-triangle", "lem-exc-constant-tensor", "lem-exc-direct-image-coproducts", "lem-exc-residue-tor-test"]
+++
Let $A=\mathcal O_E/\varpi_E^n$. Let $i:Z\hookrightarrow T$
be a closed immersion with
quasi-compact open complement $j$. Suppose $R^qj_*$ vanishes on all module
sheaves for $q>c$, takes
constructible sheaves
to constructible sheaves in every degree. The functor $Rj_*$ is
the derived direct image.
If $K$ is bounded constructible with
Tor amplitude in $[a,b]$,
then $Ri^!K$ is bounded constructible with Tor amplitude in
$[a,b+c+1]$.

## Proof

Constructibility is [lem-exc-closed-amplitude].
The quasi-compact open immersion is quasi-separated, so
[lem-exc-direct-image-coproducts] proves coproduct compatibility
from the stated cohomological-dimension bound. Put
$\kappa=A/(\varpi_E)$. Tensor the triangle of
[lem-exc-closed-support-triangle], for the right adjoint $Ri^!$
of [lem-exc-closed-ambient], with $\kappa$ and apply
[lem-exc-constant-tensor] to its third term. Exact closed
direct image commutes with this constant derived tensor: this is checked
on etale stalks, where its value is either the original module or zero.
The triangle is therefore the closed-support triangle of
$K\otimes_A^L\kappa$. By
[lem-exc-residue-tor-test], this input has cohomology in
$[a,b]$. The amplitude computation of
[lem-exc-closed-amplitude] places the first term in
$[a,b+c+1]$. A second use of
[lem-exc-residue-tor-test] proves the asserted Tor bound.
