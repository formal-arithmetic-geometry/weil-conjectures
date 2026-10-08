+++
id = "cor-cbc-proper-coincidence"
kind = "theorem"
title = "Proper morphisms: compact supports equal direct image"
order = 1876
tags = ["latex:corollary"]
uses = ["def-cbc-exchange-map", "def-compact-support-direct-image-detailed", "def-weil-pbc-derived-exchange", "def-weil-pbc-scheme-conventions", "thm-cbc-finite-torsion"]
lean = ["AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar"]
+++
For a proper
$f:X\to Y$ and the canonical identification
$Rf_!\xrightarrow{\sim}Rf_*$ of
[def-compact-support-direct-image-detailed] (the compactification
$j=\operatorname{id}$, $p=f$), the map $\operatorname{Ex}_!$
of [def-cbc-exchange-map] is the proper-base-change exchange map
of [def-weil-pbc-derived-exchange]; consequently the
compact-support base change of
[thm-cbc-finite-torsion] specializes to proper base change for
proper $f$.

## Proof

For $j=\operatorname{id}$ the extension-by-zero identification
of [def-cbc-exchange-map] is the identity, so
$\operatorname{Ex}_!$ is the exchange map of
[def-weil-pbc-derived-exchange] for the proper $p=f$, by
[def-cbc-exchange-map] and the identification
$Rf_!=Rf_*$ of [def-compact-support-direct-image-detailed].
