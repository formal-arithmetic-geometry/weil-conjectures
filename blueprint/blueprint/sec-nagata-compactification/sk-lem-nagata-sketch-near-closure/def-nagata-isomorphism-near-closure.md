+++
id = "def-nagata-isomorphism-near-closure"
kind = "definition"
title = "Modification making a proper map an isomorphism near a closure"
order = 259
lean = ["AlgebraicGeometry.exists_admissibleBlowup_isIso_strictTransformMap_near_closure"]
uses = ["cor-nagata-blowup-product-common-refinement", "def-nagata-admissible-blowup", "def-nagata-affine-blowup", "def-nagata-affine-blowup-chart-map", "def-nagata-affine-blowup-restriction-map", "def-nagata-affine-proj", "def-nagata-blowup-product-comparison", "def-nagata-blowup-product-domination-maps", "def-nagata-compactifiable", "def-nagata-compactification", "def-nagata-effective-cartier-ideal", "def-nagata-elimination-indeterminacy", "def-nagata-extended-admissible-blowup", "def-nagata-extended-ideal", "def-nagata-global-blowup", "def-nagata-global-blowup-glue-data", "def-nagata-global-blowup-local-model", "def-nagata-global-blowup-overlap-basic-map", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-invertible-ideal", "def-nagata-maximal-isomorphism-open", "def-nagata-proj-closed-center-finite-degree", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "def-nagata-scheme-image-factor", "def-nagata-separate-constructible-closed", "def-nagata-spectral-constructible-separation", "def-nagata-strict-transform", "lemma-nagata-affine-blowup-complement", "lemma-nagata-blowup-invertible-factor", "lemma-nagata-blowup-proper", "lemma-nagata-composition-center-ideal", "lemma-nagata-elimination-indeterminacy", "lemma-nagata-extend-admissible-blowup", "lemma-nagata-global-blowup-overlap-basic", "lemma-nagata-ideal-unit-off-support", "lemma-nagata-invertible-ideal-tensor-power", "lemma-nagata-localization-ideal-pow", "lemma-nagata-maximal-isomorphism-open", "lemma-nagata-product-ideal-common-blowup", "lemma-nagata-proper-to-separated-target", "lemma-nagata-rees-degree-one-element", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-generators-cover-proj", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul", "lemma-nagata-separate-constructible-closed", "lemma-nagata-spectral-constructible-separation-exists", "lemma-nagata-strict-transform-closure-characterization", "prop-nagata-affine-blowup-chart", "prop-nagata-global-blowup-cover-independent", "prop-nagata-proj-standard-open", "prop-nagata-rees-graded", "thm-nagata-blowup-principalizes-center", "thm-nagata-blowup-product-ideal", "thm-nagata-blowup-universal-property", "thm-nagata-global-blowup-proper", "thm-nagata-strict-transform-is-blowup"]
+++
Let $X$ be qcqs, let $q\colon Z\to X$ be proper, let $V\subseteq X$ be a
quasi-compact open, set
$U=q^{-1}(V)$, and let $T\subseteq V$ be closed. Assume $U\to V$ is an
isomorphism over an open neighbourhood of $T$. Let $E\subseteq V$ be
the complement of $\operatorname{IsoOpen}(U\to V)$ from
[def-nagata-maximal-isomorphism-open].
Apply [def-nagata-spectral-constructible-separation] to $(T,E)$ and
denote the output by $(T_c,E_c)$. Perform the explicitly constructed
$V$-admissible separation blow-up

$$
X_1=\mathsf{CSepBl}_V(T_c,E_c).
$$

Let $\overline E_c$ denote the topological closure of the underlying subset
of $E_c$ in $X_1$, and let
$X_0=X_1\setminus\overline E_c$ and let $q_0\colon Z_0\to X_0$ be the
restriction of the strict transform of $q$. Form
$X_0^{\mathrm{el}}(q_0,V\setminus E_c)$ and extend this admissible blow-up
to $X_1$ by [def-nagata-extended-admissible-blowup]. Define
$\mathsf{IsoBl}_{V,T}(q)\to X$ to be the composite of these two
$V$-admissible blow-ups, represented as one blow-up by the composition
construction.
