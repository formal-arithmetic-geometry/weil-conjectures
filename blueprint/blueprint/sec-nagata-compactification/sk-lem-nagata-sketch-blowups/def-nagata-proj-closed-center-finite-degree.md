+++
id = "def-nagata-proj-closed-center-finite-degree"
kind = "definition"
title = "Finite-degree data attached to a closed center in Proj"
order = 130
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.exists_finiteDegree_center", "AlgebraicGeometry.Scheme.IdealSheafData.exists_finiteDegree_center_le_blowup"]
uses = ["def-nagata-affine-blowup", "def-nagata-affine-blowup-chart-map", "def-nagata-affine-blowup-restriction-map", "def-nagata-affine-proj", "def-nagata-extended-ideal", "def-nagata-global-blowup", "def-nagata-global-blowup-glue-data", "def-nagata-global-blowup-local-model", "def-nagata-global-blowup-overlap-basic-map", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "def-nagata-relative-proj", "lemma-nagata-affine-blowup-complement", "lemma-nagata-chart-extended-ideal-principal", "lemma-nagata-dense-flat-pullback", "lemma-nagata-extended-ideal-affine-chart", "lemma-nagata-finite-type-ideal-extension-exists", "lemma-nagata-global-blowup-overlap-basic", "lemma-nagata-ideal-unit-off-support", "lemma-nagata-localization-ideal-pow", "lemma-nagata-proj-closed-center-finite-degree-exists", "lemma-nagata-rees-degree-one-element", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-generators-cover-proj", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul", "prop-nagata-affine-blowup-chart", "prop-nagata-global-blowup-cover-independent", "prop-nagata-proj-standard-open", "prop-nagata-rees-graded"]
+++
Let $\mathcal I$ be a finite type quasi-coherent ideal on a qcqs scheme
$X$, let $\mathcal A=\bigoplus_{n\geq0}\mathcal I^n$, let
$X'=\operatorname{Proj}_X(\mathcal A)$, and let
$Z'\hookrightarrow X'$ be of finite presentation. Select, by classical
choice from the nonempty witness type supplied by
[lemma-nagata-proj-closed-center-finite-degree-exists], a pair
$(d,\mathcal F)$. No property of the selected pair is built into this
definition. Denote it by
$\mathsf{FD}(Z')=(d(Z'),\mathcal F(Z'))$.

## Properties of the finite-degree center data

The selected integer $d(Z')$ is positive, $\mathcal F(Z')$ is a finite
type submodule of $\mathcal I^{d(Z')}$, and

$$
Z'=\operatorname{Proj}_X
\bigl(\mathcal A/\mathcal F(Z')\mathcal A\bigr).
$$

Moreover the support of
$\mathcal I^{d(Z')}/\mathcal F(Z')$ lies over the underlying topological
image $b(|Z'|)$ together with the first center.

*Proof.*
These are the properties required of the witness selected in
[def-nagata-proj-closed-center-finite-degree]; existence of such a
witness is
[lemma-nagata-proj-closed-center-finite-degree-exists].
