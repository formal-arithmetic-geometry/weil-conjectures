+++
id = "def-nagata-strict-transform-blowup-comparison"
kind = "definition"
title = "Comparison from the extended-ideal blow-up to the base change"
order = 158
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.isClosedImmersion_pullbackLift_blowup_comap"]
uses = ["def-nagata-affine-blowup", "def-nagata-affine-blowup-chart-map", "def-nagata-affine-blowup-restriction-map", "def-nagata-affine-proj", "def-nagata-effective-cartier-ideal", "def-nagata-extended-ideal", "def-nagata-global-blowup", "def-nagata-global-blowup-glue-data", "def-nagata-global-blowup-local-model", "def-nagata-global-blowup-overlap-basic-map", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-invertible-ideal", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "def-nagata-strict-transform", "lemma-nagata-global-blowup-overlap-basic", "lemma-nagata-localization-ideal-pow", "lemma-nagata-rees-degree-one-element", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-generators-cover-proj", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul", "lemma-nagata-strict-chart-map-surjective", "prop-nagata-affine-blowup-chart", "prop-nagata-global-blowup-cover-independent", "prop-nagata-proj-standard-open", "prop-nagata-rees-graded", "thm-nagata-blowup-principalizes-center", "thm-nagata-blowup-universal-property"]
+++
Let $f\colon Y\to X$, let $\mathcal I$ be a quasi-coherent ideal on $X$,
and put $X'=\operatorname{Bl}_{\mathcal I}(X)$. The pullback of
$\mathcal I$ to $\operatorname{Bl}_{\mathcal I\mathcal O_Y}(Y)$ is the
invertible exceptional ideal of $\mathcal I\mathcal O_Y$, so the universal
property of the blow-up ([thm-nagata-blowup-universal-property],
Stacks Tag 0806) provides a unique lift
$\rho\colon\operatorname{Bl}_{\mathcal I\mathcal O_Y}(Y)\to X'$ of the
composite to $X$. Define the *comparison morphism*

$$
\psi_{f,\mathcal I}\colon
\operatorname{Bl}_{\mathcal I\mathcal O_Y}(Y)\longrightarrow
Y\times_XX'
$$

with components the structure morphism of
$\operatorname{Bl}_{\mathcal I\mathcal O_Y}(Y)$ and the lift $\rho$.
The morphism $\psi_{f,\mathcal I}$ is a closed immersion: this is
Zariski-local on $Y\times_XX'$, and over an affine open
$V=\operatorname{Spec}(B)\subseteq Y$ lying over an affine open
$\operatorname{Spec}(A)\subseteq X$ and a standard chart of $X'$ at
$a\in I$, it is the $\operatorname{Spec}$ of the canonical ring map
$B\otimes_AA[I/a]\to B[IB/\varphi(a)]$, which is surjective because a
fraction $y/\varphi(a)^n$ with $y\in I^nB$ is a $B$-linear combination of
fractions $\varphi(z)/\varphi(a)^n$ with $z\in I^n$.
