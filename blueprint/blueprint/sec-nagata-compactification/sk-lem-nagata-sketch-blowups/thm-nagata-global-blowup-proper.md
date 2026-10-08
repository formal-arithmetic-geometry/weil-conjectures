+++
id = "thm-nagata-global-blowup-proper"
kind = "theorem"
title = "Properness of the global blow-up"
order = 92
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.isProper_blowupMap"]
uses = ["def-nagata-global-blowup", "lemma-nagata-global-blowup-proper-local", "lemma-nagata-projective-target-local", "prop-nagata-global-blowup-cover-independent"]
+++
If $\mathcal I$ is of finite type, then
$b_{X,\mathcal I}$ is proper.

## Proof

Apply [lemma-nagata-global-blowup-proper-local] to the affine open cover
of $X$. Each restricted morphism is proper, and
[lemma-nagata-projective-target-local] is the verified target-local
properness lemma (despite its historical label). It follows that
$b_{X,\mathcal I}$ is proper. This argument does not use the unresolved
global projectivity theorem.
