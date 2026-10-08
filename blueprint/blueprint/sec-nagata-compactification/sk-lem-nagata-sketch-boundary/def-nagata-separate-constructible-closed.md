+++
id = "def-nagata-separate-constructible-closed"
kind = "definition"
title = "Constructible-boundary separation blow-up"
order = 250
lean = ["AlgebraicGeometry.exists_admissibleBlowup_disjoint_closures"]
uses = ["def-nagata-admissible-blowup", "def-nagata-constructible-closed-support", "def-nagata-extended-ideal", "def-nagata-finite-type-ideal-extension", "def-nagata-global-blowup", "def-nagata-qc-open-complement-ideal", "def-nagata-scheme-image-factor", "def-nagata-separate-closed-subschemes", "def-nagata-strict-transform", "lemma-nagata-constructible-closed-support", "lemma-nagata-extend-finite-type-ideal", "lemma-nagata-qc-open-complement-ideal", "lemma-nagata-qc-open-complement-ideal-exists", "lemma-nagata-separate-closed-subschemes", "lemma-nagata-strict-transform-closure-characterization", "prop-nagata-global-blowup-cover-independent"]
+++
Let $X$ be qcqs, let $U\subseteq X$ be a quasi-compact open, and let
$T_1,T_2\subseteq U$ be disjoint constructible subsets closed in $U$.
Define

$$
\mathcal J_i=\mathcal J_U(T_i),\qquad
\mathcal I_i=\operatorname{Ext}_{X,U}(\mathcal J_i),\qquad
Z_i=V(\mathcal I_i),
$$

and set

$$
\mathsf{CSepBl}_U(T_1,T_2)
=\mathsf{SepBl}_U(Z_1,Z_2).
$$
