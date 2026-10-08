+++
id = "lemma-weil-pbc-finite-direct-image-exact"
kind = "lemma"
title = "Exactness of finite direct image"
order = 998
lean = ["AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isFinite", "AlgebraicGeometry.Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory"]
uses = ["def-kun-separably-closed", "def-weil-pbc-direct-image", "def-weil-pbc-geometric-fibre", "def-weil-pbc-geometric-stalks", "def-weil-pbc-scheme-conventions", "lemma-openclosed-point-ulift", "lemma-weil-pbc-finite-stalk-formula", "lemma-weil-pbc-geometric-stalk-conservative"]
+++
If $h$ is finite, then $h_*$ on etale abelian sheaves is exact.

## Proof

For a short exact sequence $0\to F_1\to F_2\to F_3\to0$, apply the stalk
formula at every geometric $\bar v$. A finite product of short exact
sequences of abelian groups is exact, so the sequence of stalks of the direct
images is exact. Geometric stalks are conservative for etale sheaves:
injectivity and surjectivity can be checked after an etale neighbourhood of
each geometric point and then sheafified. Hence the direct-image sequence is
exact. Consequently the total right derived functor $Rh_*$ is $h_*$ applied levelwise to
complexes, and in particular $R^qh_*=0$ for $q>0$; only the first of these two consequences
is formalised.

## Detailed form

For finite $f$, the functor $f_*:\Ab(X_{\Et})\to\Ab(Y_{\Et})$ is exact.
Consequently $R^qf_*=0$ for $q>0$ and $Rf_*=f_*$ on $\Dplus(X_{\Et})$.

## Proof

By [lemma-weil-pbc-finite-stalk-formula], a short exact sequence of sheaves
becomes, at every geometric stalk of the target, a finite direct sum of short
exact sequences at the geometric points of the finite fibre; since the stalk
functors are exact and jointly conservative, $f_*$ is exact. The vanishing of
the higher derived functors follows.
