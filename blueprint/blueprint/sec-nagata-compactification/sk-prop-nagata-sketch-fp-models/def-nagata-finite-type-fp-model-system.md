+++
id = "def-nagata-finite-type-fp-model-system"
kind = "definition"
title = "Finite-presentation model system of a finite-type morphism"
order = 389
lean = ["AlgebraicGeometry.Scheme.Hom.FinitePresentationApproximation"]
uses = ["def-nagata-closed-subscheme-fp-system", "def-nagata-immersion-into-fp-model", "def-nagata-immersion-shrink-to-closed"]
+++
For $X\to S$ locally of finite type with $X$ qcqs and $S$ qcqs, form
$i^{\mathrm{imm}}\colon X\to Y^{\mathrm{imm}}$, set
$Y^\circ=Y^{\mathrm{cl}}(i^{\mathrm{imm}})$, and apply
[def-nagata-closed-subscheme-fp-system] to
$X\hookrightarrow Y^\circ$. Denote the resulting system by

$$
\mathsf{FP}(X/S)=(A_{X/S},(X_\alpha)_\alpha),
$$

with structural maps $i_\alpha\colon X\to X_\alpha$.
