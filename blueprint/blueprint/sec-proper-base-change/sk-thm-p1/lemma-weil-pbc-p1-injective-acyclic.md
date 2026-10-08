+++
id = "lemma-weil-pbc-p1-injective-acyclic"
kind = "lemma"
title = "Acyclicity of injectives on $\\mathbf P^1_s$"
order = 1141
uses = ["lemma-weil-pbc-h1-constructible-representation", "lemma-weil-pbc-h1-torsor-comparison", "lemma-weil-pbc-injective-restriction-acyclicity"]
+++
For an injective sheaf $I$ of $\mathbf F_\ell$-modules on
$X=\mathbf P^1_A$, the restriction
$I_0$ is $\Gamma(X_0,-)$-acyclic: $H^q(X_0,I_0)=0$ for all $q>0$.

## Proof

The affine-cover lemma gives vanishing for $q>1$ because $\mathbf P^1$ is
covered by two affines. For $q=1$, apply the representation lemma. For each
finite summand, finite-direct-image exactness and Leray identify its $H^1$ on
$X_0$ with $H^1((V_i)_0,\underline{M_i})$. Torsor comparison lifts every
component to $H^1(V_i,\underline{M_i})$, and Leray returns a class in
$H^1(X,(h_i)_*\underline{M_i})$. Their finite sum maps to zero in $H^1(X,I)$
because $I$ is injective. Restriction of the commuting square shows that the
original class is zero. The source locator is Tag `0A5H`.
