+++
id = "rem-sf-finite-level-comparison-ingredient"
kind = "remark"
title = "The local-model proof and normalized DVR reconstruction"
order = 2208
uses = ["cor-coef-finite-verdier", "def-coef-normalized-dvr-tower", "def-weil-pbc-bounded-constructible-tower", "lem-coef-finite-direct-image", "lem-coef-finite-exceptional", "lem-coef-integral-hom-reduction", "lem-coef-normalized-dvr-effectivity", "prop-coef-integral-exceptional-adjoint"]
+++
The proof of *The finite-level comparison isomorphisms of the package, from uniform local models* uses the uniform
local models of [def-weil-pbc-bounded-constructible-tower].
The two sufficient criteria
*Stage-independent local models for a constant tower*, *Stage-independent local models for a lisse tower with a uniform trivializing cover*
retain all of their lisse and amplitude hypotheses, and
*The finite-level comparison isomorphisms in the two cases* applies under those
complete hypotheses. These results provide additional local-model
information; they are not necessary hypotheses for DVR reconstruction.

The separate theorem [lem-coef-normalized-dvr-effectivity]
reconstructs every coherent normalized DVR tower of
[def-coef-normalized-dvr-tower], without a common stratification
or common lisse model. With finite-level constructibility and a
uniform amplitude bound it yields an object of the integral category.
The direct-image and duality towers have their normalization maps from
[lem-coef-finite-direct-image], [cor-coef-finite-verdier]; the
exceptional tower has them from [lem-coef-finite-exceptional].
General internal-Hom reduction and the integral exceptional adjunction
are independently established in
[lem-coef-integral-hom-reduction], [prop-coef-integral-exceptional-adjoint].
For an arbitrary tower whose normalization has not been checked,
merely taking its derived limit still supplies no identification with
the proposed finite reductions.
