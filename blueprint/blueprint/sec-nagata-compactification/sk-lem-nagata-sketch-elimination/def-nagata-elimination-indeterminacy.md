+++
id = "def-nagata-elimination-indeterminacy"
kind = "definition"
title = "Elimination-of-indeterminacy construction"
order = 228
lean = ["AlgebraicGeometry.exists_admissibleBlowup_isOpenImmersion_strictTransformMap"]
uses = ["cor-nagata-blowup-product-common-refinement", "cor-nagata-conrad-proper-target-extension", "def-nagata-admissible-blowup", "def-nagata-compactifiable", "def-nagata-compactification", "def-nagata-composition-of-blowups-comparison", "def-nagata-conrad-quasi-domination", "def-nagata-constructible-closed-support", "def-nagata-dense-compactification", "def-nagata-global-blowup", "def-nagata-qc-open-complement-ideal", "def-nagata-scheme-image-comparison", "def-nagata-strict-transform", "lemma-nagata-admissible-blowup-comp", "lemma-nagata-admissible-blowup-over-open", "lemma-nagata-admissible-blowup-preserves-density", "lemma-nagata-blowup-proper", "lemma-nagata-composition-center-ideal", "lemma-nagata-composition-extended-ideal-equality", "lemma-nagata-conrad-schematically-dense-blowup", "lemma-nagata-constructible-closed-support", "lemma-nagata-dense-flat-pullback", "lemma-nagata-qc-open-complement-ideal", "lemma-nagata-qc-open-complement-ideal-exists", "lemma-nagata-scheme-image-universal", "lemma-nagata-scheme-theoretic-closure-minimal", "lemma-nagata-strict-transform-closure-characterization", "lemma-nagata-strict-transform-over-complement", "prop-nagata-global-blowup-cover-independent", "thm-nagata-composition-of-blowups", "thm-nagata-conrad-elimination", "thm-nagata-global-blowup-proper"]
+++
Let $q\colon Z\to X$ be separated and of finite type, let $X$ be qcqs, and
let $U\subseteq X$ be quasi-compact. Fix an isomorphism
$e_U\colon q^{-1}(U)\xrightarrow{\sim}U$ over $U$. The construction is the
bridge of [the-general-case-via-zariski-s-main-theorem--remark-2], with each
choice labelled.

1. By [lemma-nagata-conrad-schematically-dense-blowup], select a finite type
ideal $\mathcal I_0$ with $V(\mathcal I_0)=X\setminus U$ and put
$X_1=\operatorname{Bl}_{\mathcal I_0}(X)$, a $U$-admissible blow-up in which
$U$ is scheme-theoretically dense. Let $q_1\colon Z_1\to X_1$ be the strict
transform of $Z$; it is separated, of finite type, and an isomorphism over
$U$.
1. The section $s\colon U\cong q_1^{-1}(U)\hookrightarrow Z_1$ induced by
$e_U$ is a quasi-domination $(U,s)$ of $U$ over $Z_1$
([def-nagata-conrad-quasi-domination]). Apply
[thm-nagata-conrad-elimination] over the base $X_1$ with $V=U$, and select
the resulting $U$-admissible centre $\mathcal I$ on $X_1$ together with the
quasi-domination $(W,\widetilde s)$ of $\operatorname{Bl}_{\mathcal I}(X_1)$
over $Z_1$ extending $s$.
1. Let $\mathcal I_1=\mathcal I_0\mathcal O_{X_1}$, so that
$V(\mathcal I_1)=X_1\setminus U$. Define

$$
X^{\mathrm{el}}(q,U)=\operatorname{Bl}_{\mathcal I\mathcal I_1}(X_1),
\qquad
Z^{\mathrm{el}}(q,U)=\operatorname{ST}_{X^{\mathrm{el}}/X}(Z),
$$

together with the strict-transform projection
$q^{\mathrm{el}}\colon Z^{\mathrm{el}}(q,U)\to X^{\mathrm{el}}(q,U)$ and
the transported open identification induced by $e_U$. By
[cor-nagata-blowup-product-common-refinement], $X^{\mathrm{el}}(q,U)$
dominates $\operatorname{Bl}_{\mathcal I}(X_1)$ over $X_1$, and by
[lemma-nagata-admissible-blowup-comp] the composite
$X^{\mathrm{el}}(q,U)\to X_1\to X$ is a $U$-admissible blow-up of $X$
([def-nagata-admissible-blowup]).

The centres $\mathcal I_0$ and $\mathcal I$ are labelled selections, so
$X^{\mathrm{el}}(q,U)$ is a named object rather than an unspecified
existential variable.
