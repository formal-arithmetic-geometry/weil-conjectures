+++
id = "lemma-nagata-rees-generators-cover-proj"
kind = "lemma"
title = "Degree-one generators cover Proj"
order = 35
lean = ["AlgebraicGeometry.AffineBlowup.iSup_basicOpen_reesX_eq_top"]
uses = ["def-nagata-affine-proj", "def-nagata-rees-algebra", "def-nagata-rees-piece", "lemma-nagata-rees-degree-one-element", "lemma-nagata-rees-piece-membership", "prop-nagata-proj-standard-open", "prop-nagata-rees-finite-generation", "prop-nagata-rees-graded"]
+++
If $I=(f_0,\ldots,f_r)$, then the standard opens
$D_+(f_it)$ cover $\operatorname{Proj}(\mathcal R_A(I))$.

## Proof

The elements $f_it$ generate the irrelevant ideal by
[prop-nagata-rees-finite-generation]. Apply
[prop-nagata-proj-standard-open] (`AlgebraicGeometry.Proj.iSup_basicOpen_eq_top`) to obtain the
asserted cover (in Lean, the lemma is that application to the Rees grading, with the
generation statement `irrelevant_le_span_range_reesX`); equivalently, a homogeneous prime cannot contain all
generators.
