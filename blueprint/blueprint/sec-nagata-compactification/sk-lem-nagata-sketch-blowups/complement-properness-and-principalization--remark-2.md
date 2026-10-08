+++
id = "complement-properness-and-principalization--remark-2"
kind = "remark"
title = "Formalization route"
order = 100
+++
The formal statement (`extendedToBlowup_isEffectiveCartier`) proves
the effective-Cartier form only, directly from
[lemma-nagata-chart-extended-ideal-principal] and
[lemma-nagata-chart-generator-regular]: being effective Cartier is a
local condition, so the gluing step through
[lemma-nagata-chart-generators-associated] and the invertible-sheaf
half ([def-nagata-invertible-ideal],
[lemma-nagata-effective-cartier-is-invertible],
[lemma-nagata-invertible-ideal-is-effective-cartier]) are not needed
and are not formalized. The Lean theorem also requires no finite-type
hypothesis on the center.
