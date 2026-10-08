+++
id = "lemma-constructible-iso-invariance"
kind = "lemma"
title = "Invariance under isomorphism"
order = 1161
lean = ["AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_iso", "AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.of_iso", "AlgebraicGeometry.Scheme.IsFiniteSheaf.of_iso", "AlgebraicGeometry.Scheme.IsLocallyConstantSheaf.of_iso"]
uses = ["def-constructible-constant", "def-constructible-constructible", "def-constructible-finite", "def-constructible-finite-locally-constant", "def-constructible-locally-constant", "def-constructible-stratification", "def-kun-separably-closed"]
+++
If $\mathcal F\cong\mathcal F'$ in $\shv{\et X}$, then $\mathcal F$ is
locally constant (finite, finite locally constant, constructible) if and
only if $\mathcal F'$ is.

## Proof

An isomorphism of sheaves induces isomorphisms of the restrictions to every
localised site, of all stalks, and of all pullbacks, and each of the four
notions is a condition on these. A trivialising datum, respectively a
stratification, for $\mathcal F$ is therefore one for $\mathcal F'$.
