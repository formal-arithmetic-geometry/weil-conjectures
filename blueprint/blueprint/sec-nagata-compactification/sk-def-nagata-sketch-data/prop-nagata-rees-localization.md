+++
id = "prop-nagata-rees-localization"
kind = "theorem"
title = "Graded localization of the Rees algebra"
order = 40
lean = ["AlgebraicGeometry.AffineBlowup.isLocalization_away_map"]
tags = ["latex:proposition"]
uses = ["def-nagata-homogeneous-localization-degree-zero", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "lemma-nagata-localization-ideal-pow", "lemma-nagata-localization-rees-piece", "lemma-nagata-rees-degree-one-element", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul", "prop-nagata-rees-graded"]
+++
The map $\rho_s$ is a graded ring equivalence.

## Proof

For each $n$, let $\rho_{s,n}$ be the equivalence of
[lemma-nagata-localization-rees-piece]. Taking their direct sum is
legitimate because every Rees element has finite homogeneous support. On
homogeneous tensors of degrees $m,n$, both ways around the multiplication
square have coefficient $(xy)/1$ in degree $m+n$; the equality of localized
ideal powers from [lemma-nagata-localization-ideal-pow] proves
multiplicativity. The direct sum of the inverse maps is constructed in
the same way, and the two composites are identities in each degree, hence
on finite sums. This gives the claimed graded ring equivalence.
