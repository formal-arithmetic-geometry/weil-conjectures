+++
id = "lemma-nagata-affine-blowup-proper"
kind = "lemma"
title = "Properness of the affine blow-up"
order = 90
lean = ["AlgebraicGeometry.AffineBlowup.isProper_toSpec"]
uses = ["def-nagata-affine-blowup", "def-nagata-affine-proj", "def-nagata-rees-algebra", "def-nagata-rees-piece", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-piece-mul", "prop-nagata-rees-finite-generation", "prop-nagata-rees-graded"]
+++
If $I$ is finitely generated, the affine blow-up morphism is proper.

## Proof

By [def-nagata-affine-blowup], the affine blow-up is
$\operatorname{Proj}(\mathcal R_A(I))\to\operatorname{Spec}A$, the
structural morphism of Proj followed by the isomorphism
$\operatorname{Spec}\mathcal R_A(I)_0\cong\operatorname{Spec}A$ induced by
$\mathcal R_A(I)_0\cong A$ ([lemma-nagata-rees-degree-zero]), with the grading of [prop-nagata-rees-graded].
Since $I$ is finitely generated, the Rees algebra is of finite type over
its degree-zero part ([prop-nagata-rees-finite-generation]). The
verified properness instance for $\operatorname{Proj}$ of a graded ring of
finite type over its degree-zero part ([def-nagata-affine-proj]) makes the
structural morphism proper, and composing with an isomorphism keeps it
proper.
