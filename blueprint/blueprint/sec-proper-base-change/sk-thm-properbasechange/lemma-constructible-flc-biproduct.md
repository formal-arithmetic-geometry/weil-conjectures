+++
id = "lemma-constructible-flc-biproduct"
kind = "lemma"
title = "Finite direct sums"
order = 1295
lean = ["AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.biprod", "AlgebraicGeometry.Scheme.IsFiniteSheaf.biprod", "AlgebraicGeometry.Scheme.IsLocallyConstantSheaf.biprod", "CategoryTheory.Sheaf.IsConstant.biprod"]
uses = ["def-constructible-constant", "def-constructible-finite", "def-constructible-finite-locally-constant", "def-constructible-locally-constant", "def-kun-separably-closed", "lemma-constructible-common-refinement", "lemma-constructible-pullback-constant", "lemma-constructible-pullback-locally-constant"]
+++
Finite direct sums of finite locally constant sheaves are finite locally
constant; the same holds for locally constant sheaves and for finite
sheaves.

## Proof

For two sheaves with trivialising data $(U_i\to X)_i$ and $(V_j\to X)_j$,
the family $(U_i\times_XV_j\to X)_{i,j}$ is an étale cover trivialising
both. Restriction to a localised site is exact and preserves finite direct
sums, and a finite direct sum $M_X\oplus N_X$ of constant sheaves is the
constant sheaf $(M\oplus N)_X$, because sheafification and the constant
presheaf functor are additive. Stalks commute with finite direct sums,
and a finite direct sum of finite sets is finite.
