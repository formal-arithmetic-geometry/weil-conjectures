+++
id = "sk-prop-nagata-sketch-envelope"
kind = "section"
title = "Separated finite-presentation envelope"
order = 391
uses = ["sk-prop-nagata-sketch-fp-models"]
lean = ["AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_isSeparated_locallyOfFinitePresentation"]
+++
*Proposition (sketch).*

A separated finite-type $f:X\to S$ with $S$ qcqs factors as

$$
X\hookrightarrow X^{\mathrm{fp}}
\longrightarrow S,
$$

where the first map is a closed immersion and the second is separated
and of finite presentation.

## Proof

Use [sk-prop-nagata-sketch-fp-models]. Separatedness over a fixed
qcqs base is eventually detected in a qcqs inverse system with affine
transitions: after increasing the index the stage is separated
(01ZH). Choose such a stage as $X^{\mathrm{fp}}$;
this is 01ZJ. No finite-presentation hypothesis on the
closed immersion $X\hookrightarrow X^{\mathrm{fp}}$ is required.

Uses: [sk-prop-nagata-sketch-fp-models]
