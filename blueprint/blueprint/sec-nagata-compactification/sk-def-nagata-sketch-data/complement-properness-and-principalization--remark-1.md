+++
id = "complement-properness-and-principalization--remark-1"
kind = "remark"
title = "Formalization route"
order = 61
+++
The formal proof (`isProper_blowupMap`) follows this target-local
reduction and settles the affine case
([lemma-nagata-affine-blowup-proper]) by identifying
$\operatorname{Bl}_I(A)\to\operatorname{Spec}(A)$ with
`Proj.toSpecZero` of the Rees algebra and invoking Mathlib's
properness of $\operatorname{Proj}$ over its degree-zero part, fed by
[prop-nagata-rees-finite-generation]. Projectivity of the blow-up is therefore not needed.
