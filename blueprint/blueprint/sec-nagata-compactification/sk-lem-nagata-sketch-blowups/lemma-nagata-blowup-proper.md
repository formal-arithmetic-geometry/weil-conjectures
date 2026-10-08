+++
id = "lemma-nagata-blowup-proper"
kind = "lemma"
title = "Properness of a blow-up"
order = 163
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.isProper_blowupMap"]
uses = ["def-nagata-global-blowup", "lemma-nagata-global-blowup-proper-local", "lemma-nagata-projective-target-local", "prop-nagata-global-blowup-cover-independent", "thm-nagata-global-blowup-proper"]
+++
Let $X$ be a scheme and let $\mathcal I$ be a finite-type quasi-coherent
ideal on $X$. Its blow-up is proper over $X$. In particular,
every admissible blow-up used in this chapter is proper.

## Proof

A finite type quasi-coherent ideal defines the global blow-up of
[def-nagata-global-blowup]. Its structure map is proper by
[thm-nagata-global-blowup-proper]. An admissible blow-up is a blow-up
of precisely this form.
