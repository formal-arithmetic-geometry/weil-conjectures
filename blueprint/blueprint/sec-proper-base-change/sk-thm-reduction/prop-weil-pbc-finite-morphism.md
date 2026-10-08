+++
id = "prop-weil-pbc-finite-morphism"
kind = "theorem"
title = "Finite morphisms satisfy proper base change"
order = 1193
lean = ["AlgebraicGeometry.Etale.isBaseChangeIsoSheaf_of_isFinite", "AlgebraicGeometry.Etale.isBaseChangeIso_of_isFinite"]
tags = ["latex:proposition"]
uses = ["def-weil-pbc-derived-exchange", "def-weil-pbc-property", "def-weil-pbc-scheme-conventions", "def-weil-pbc-underived-exchange", "lemma-weil-pbc-finite-direct-image-exact", "lemma-weil-pbc-finite-exchange", "lemma-weil-pbc-property-iff-acyclicity"]
+++
Every finite morphism satisfies $\mathsf{PBC}$.

## Proof

The finite exchange lemma supplies the required isomorphism for every base
change and every torsion sheaf, which is exactly Definition
[def-weil-pbc-property]. Equivalently, the vanishing in the exactness
lemma gives $\mathsf{IA}$ and Lemma [lemma-weil-pbc-property-iff-acyclicity]
gives $\mathsf{PBC}$.

## Detailed form

Every finite morphism $f$ satisfies $\mathrm{PBC}(f)$ in the sense of
[def-weil-pbc-property].

## Proof

Finite morphisms and all their base changes are finite, so
[lemma-weil-pbc-finite-exchange] supplies the canonical exchange isomorphism for
every base change and every torsion sheaf, which is the definition of
$\mathrm{PBC}(f)$ by [def-weil-pbc-property].
