+++
id = "thm-nagata-conrad-elimination"
kind = "theorem"
title = "Elimination of indeterminacy for quasi-dominations (Conrad)"
order = 220
lean = ["AlgebraicGeometry.exists_admissibleBlowup_extend_partialSection"]
uses = ["def-nagata-admissible-blowup", "def-nagata-affine-blowup", "def-nagata-affine-blowup-chart-map", "def-nagata-affine-blowup-restriction-map", "def-nagata-affine-proj", "def-nagata-conrad-quasi-domination", "def-nagata-global-blowup", "def-nagata-global-blowup-glue-data", "def-nagata-global-blowup-local-model", "def-nagata-global-blowup-overlap-basic-map", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-quasi-affine-morphism", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "lemma-nagata-admissible-blowup-comp", "lemma-nagata-affine-blowup-complement", "lemma-nagata-blowup-proper", "lemma-nagata-conrad-blowup-base-change-reduction", "lemma-nagata-conrad-closed-target-reduction", "lemma-nagata-conrad-dense-in-admissible-blowup", "lemma-nagata-conrad-graph-closure-quasi-finite", "lemma-nagata-conrad-quasi-affine-general", "lemma-nagata-global-blowup-overlap-basic", "lemma-nagata-ideal-unit-off-support", "lemma-nagata-localization-ideal-pow", "lemma-nagata-quasi-affine-morphism-of-quasi-finite", "lemma-nagata-rees-degree-one-element", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-generators-cover-proj", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul", "lemma-nagata-scheme-image-ideal-qc", "prop-nagata-affine-blowup-chart", "prop-nagata-global-blowup-cover-independent", "prop-nagata-proj-standard-open", "prop-nagata-rees-graded", "thm-nagata-global-blowup-proper"]
+++
Let $S$ be qcqs and let $X$ and $Y$ be qcqs $S$-schemes with $Y\to S$
separated and of finite type. Let $U\subseteq V\subseteq X$ be dense open
subschemes whose open immersions into $X$ are quasi-compact, and let $(U,f)$
be a quasi-domination of $V$ over $Y$ in the sense of
[def-nagata-conrad-quasi-domination]. There exists a $V$-admissible
blow-up $\widetilde X\to X$ such that $\widetilde X$ quasi-dominates $Y$ in a
manner extending $f\colon U\to Y$.

## Proof

The morphism $f$ is automatically quasi-compact and quasi-separated.
Replacing $Y$ by $Y\times_SX$ we may assume $X=S$; thus $p\colon Y\to X$ is
separated and of finite type and $f\colon U\to Y$ is a section of $p$ over
$U$ whose image is closed in the part of $Y$ lying over $V$.

If $p$ is quasi-affine, this is
[lemma-nagata-conrad-quasi-affine-general]. In general, let
$q\colon\widetilde X\to X$ be the $V$-admissible blow-up produced by
[lemma-nagata-conrad-graph-closure-quasi-finite] and let
$\overline{F(U)}\subseteq\widetilde X\times_XY$ be the scheme-theoretic image
of $F=(\sigma,f)$. That lemma makes
$\overline{F(U)}\to\widetilde X$ quasi-finite and separated, so
[lemma-nagata-quasi-affine-morphism-of-quasi-finite] makes it
quasi-affine as a morphism to $\widetilde X$. (Note that $\widetilde X$ is a
blow-up of a qcqs scheme and is not itself quasi-affine, so the absolute form
of quasi-affineness is not available here.)

By [lemma-nagata-conrad-blowup-base-change-reduction] we may base change
along the $V$-admissible blow-up $q$ without leaving the statement of the
theorem; [lemma-nagata-conrad-dense-in-admissible-blowup] keeps $U$ and
$V$ dense. After that base change the scheme-theoretic image
$\overline{f(U)}$ of $U$ in $Y$ is quasi-affine over the base, so
[lemma-nagata-conrad-closed-target-reduction] lets us replace $Y$ by
$\overline{f(U)}$, and we are reduced to the quasi-affine case already
treated.
