+++
id = "def-nagata-global-blowup-local-model"
kind = "definition"
title = "Local blow-up model on an affine open"
order = 48
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.blowupFunctor"]
uses = ["def-nagata-affine-blowup", "def-nagata-affine-blowup-restriction-map", "def-nagata-affine-proj", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "lemma-nagata-affine-blowup-restrict-cocycle", "lemma-nagata-localization-ideal-pow", "lemma-nagata-rees-piece-membership", "prop-nagata-rees-graded"]
+++
Let $\mathcal I\subseteq\mathcal O_X$ be quasi-coherent and let
$V=\operatorname{Spec}(A)\subseteq X$ be affine. Put
$I_V=\Gamma(V,\mathcal I)\subseteq A$ and define the local model

$$
\mathsf B_V(\mathcal I)=\operatorname{Bl}_{I_V}(V)\longrightarrow V.
$$
