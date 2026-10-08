+++
id = "rem-sf-direct-image-proof-status"
kind = "remark"
title = "Status of the recorded argument for clause (iii)"
order = 2212
uses = ["cor-sf-direct-image-ctf-etale-origin", "cor-sf-direct-image-ctf-nonproper", "cor-sf-direct-image-ctf-proetale", "def-exchange-projection", "def-sf-pf", "def-sf-uniform-direct-image-vanishing", "def-weil-finite-tor-amplitude", "lem-exc-residue-tor-test", "lem-sf-comparison-tor-amplitude", "lem-sf-etale-direct-image-vanishing", "lem-sf-flat-model", "lem-sf-proetale-constructible-origin", "lem-sf-proetale-residue-tor-test", "lem-sf-projection-finite-constant", "open-sf-preservation-gaps"]
+++
The proof of clause (iii) of the finite-Tor preservation summary bounds
$\mathcal H^r(Rf_*K\otimes^L_AM)$ for an arbitrary module sheaf $M$ by
combining the projection formula for the constant coefficient sheaf
$M_Y$ with a bound ``produced by the proofs'' of the direct-image
finiteness theorems. Two points about that step are worth recording
exactly.

1. The projection transformation of [def-exchange-projection] and
[def-sf-pf] is the one for $Rf_!$, and its recorded forms require the
tensor factor to lie in the finite-Tor subcategory. The direct-image form
used in that step, with a constant tensor factor outside the finite-Tor
subcategory, is supplied by
[lem-sf-projection-finite-constant] for a finitely presented constant
coefficient; no projection formula with an *arbitrary* test sheaf is
recorded, and the proof below does not need one.
1. The uniform bound on $\mathcal H^r(Rf_*K\otimes^L_AM)$ that the
step needs, independent of $M$, is exactly the hypothesis
$\operatorname{UDV}$ of
[def-sf-uniform-direct-image-vanishing]. On the small étale site it
is a theorem, [lem-sf-etale-direct-image-vanishing], for every
finite-type morphism, so clause (iii) is unconditional there, by
[cor-sf-direct-image-ctf-nonproper]. On the small pro-étale site
the bound is *not* used at all in the route taken here: the cell is
reduced to the étale one. By
[lem-sf-proetale-constructible-origin] every object of
$D^b_{ctf}(X_{\Proet},A)$ is of étale origin, and
[lem-sf-comparison-tor-amplitude] transfers the finite-Tor condition
across the comparison in both directions, so
[cor-sf-direct-image-ctf-proetale] proves clause (iii) at the finite
coefficient stages for *every* object of
$D^b_{ctf}(X_{\Proet},A)$, with the amplitude $[a,b+2d]$, through
[cor-sf-direct-image-ctf-nonproper] and the comparison direct image.
The earlier corollary [cor-sf-direct-image-ctf-etale-origin] remains
the special case of objects presented with an explicit étale model. In
particular the transport no longer needs a pro-étale analogue of the
residue test as an input: such a test is now a theorem,
[lem-sf-proetale-residue-tor-test], proved from the origin statement
and the transfer of the finite-Tor condition. What is still recorded in
[open-sf-preservation-gaps] is not the direct-image cell but the
internal-Hom cell and the full-cohomological-dimension interface.

The step that passes from a constant test sheaf to an arbitrary one is the
residue test [lem-exc-residue-tor-test], which is available for
bounded constructible complexes on the small étale site; the flat model
[lem-sf-flat-model] is what produces the cohomological interval of
$K$, and hence the interval of the test complex
$K\otimes^L_A\kappa_X$.
