+++
id = "rem-sf-preservation-matrix"
kind = "remark"
title = "Preservation results and their actual hypotheses"
order = 2216
uses = ["cor-coef-integral-internal-hom", "cor-sf-direct-image-ctf-proetale", "cor-sf-hom-ctf-proetale-unconditional", "cor-weil-boundary-duality-discharge", "lem-coef-integral-hom-reduction", "lem-coef-normalized-dvr-effectivity", "lem-sf-pullback-tor-amplitude", "lem-sf-tensor-ctf", "prop-coef-integral-exceptional-adjoint", "rem-sf-proetale-hom-status", "rem-sf-tower-shapes-occurring", "thm-sf-biduality-class", "thm-sf-hom-ctf", "thm-sf-preservation-class"]
+++
The finite-coefficient results used in the assembly have these scopes:

1. Pullback preserves finite Tor amplitude by
[lem-sf-pullback-tor-amplitude]; tensor products have the bound of
[lem-sf-tensor-ctf].
1. Ordinary direct image on the constructible comparison class has the
geometric dimension bound of [cor-sf-direct-image-ctf-proetale].
1. The internal-Hom bound $[c-b,d-a]$ requires a site-perfect first
variable in [thm-sf-hom-ctf], [cor-sf-hom-ctf-proetale-unconditional].
The former general bound is false; [rem-sf-proetale-hom-status]
records the geometric obstruction. The dimension-dependent bound in
[thm-sf-hom-ctf] proves preservation for a general finite-Tor
constructible first variable.
1. Exceptional preservation is [thm-sf-preservation-class].
The dualizing object and general finite-coefficient geometric dual bound
are [lem-weil-verdier-preservation-strata]. General finite-stage biduality is
[thm-sf-biduality-class]; closed-boundary exchange follows in
[cor-weil-boundary-duality-discharge].
1. Integral Hom reduction and preservation are
[lem-coef-integral-hom-reduction], [cor-coef-integral-internal-hom];
the exceptional adjunction is [prop-coef-integral-exceptional-adjoint].
Normalized DVR towers reconstruct by [lem-coef-normalized-dvr-effectivity].
The scope for other towers is [rem-sf-tower-shapes-occurring].

This record collects results and supplies no premise to their proofs.
