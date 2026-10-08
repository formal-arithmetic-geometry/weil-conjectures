+++
id = "def-nagata-global-blowup-overlap-basic-map"
kind = "definition"
title = "Basic-overlap comparison map"
order = 49
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.isPullback_blowupNatTrans_of_basicOpen"]
uses = ["def-nagata-affine-blowup", "def-nagata-affine-blowup-restriction-map", "def-nagata-affine-proj", "def-nagata-global-blowup-local-model", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "lemma-nagata-localization-ideal-pow", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul", "prop-nagata-affine-blowup-restrict", "prop-nagata-rees-graded"]
+++
If a basic affine open $D(s)$ lies in $V_i\cap V_j$, define

$$
\omega_{ij,s}\colon
\mathsf B_{V_i}(\mathcal I)|_{D(s)}
\longrightarrow
\mathsf B_{V_j}(\mathcal I)|_{D(s)}
$$

as $r_{j,s}\circ r_{i,s}^{-1}$: first use the inverse of the restriction
isomorphism $r_{i,s}$ to move from the first local model to the blow-up of
the localized ideal, and then use $r_{j,s}$ to reach the second local model.
Both restriction maps have the blow-up of the same localized ideal as their
common source.
