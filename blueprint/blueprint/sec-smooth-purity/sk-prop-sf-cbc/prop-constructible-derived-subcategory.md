+++
id = "prop-constructible-derived-subcategory"
kind = "theorem"
title = "The constructible derived category"
order = 1523
lean = ["AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible_isTriangulated", "AlgebraicGeometry.Etale.DerivedCategory.constructibleHomology_isTriangulated", "DerivedCategory.homologyProperty_isTriangulated"]
tags = ["latex:proposition"]
uses = ["def-constructible-constant", "def-constructible-constructible", "def-constructible-finite", "def-constructible-finite-locally-constant", "def-constructible-locally-constant", "def-constructible-stratification", "def-kun-separably-closed", "lemma-constructible-iso-invariance", "lemma-constructible-pullback-locally-constant", "thm-constructible-serre"]
+++
Let $\mathcal A=\mathrm{Mod}_\Lambda$ with $\Lambda$ a finite ring. The
full subcategory $D^b_c(\et X)$ of the bounded derived category
$D^b(\shv{\et X})$ consisting of the complexes all of whose cohomology
sheaves are constructible is a triangulated subcategory.

## Proof

For a weak Serre subcategory $\mathcal C$ of an abelian category, the
complexes with cohomology in $\mathcal C$ form a triangulated subcategory
of the derived category: the zero object and shifts are clear, and for a
distinguished triangle $K\to L\to M\to K[1]$ with $K$ and $M$ having
cohomology in $\mathcal C$, the long exact cohomology sequence
$H^{n}(K)\to H^n(L)\to H^n(M)$ exhibits $H^n(L)$ as an extension of a
subobject of $H^n(M)$ (a kernel) by a quotient of $H^n(K)$ (a cokernel),
both in $\mathcal C$, hence $H^n(L)\in\mathcal C$. Apply this to the weak
Serre subcategory of [thm-constructible-serre]. (In the formalisation the
general statement is `DerivedCategory.homologyProperty_isTriangulated`, for any
property of objects closed under isomorphisms, kernels, cokernels and extensions; it is
applied to the constructible sheaves with these closure properties, the content of
[thm-constructible-serre], as hypotheses.)
