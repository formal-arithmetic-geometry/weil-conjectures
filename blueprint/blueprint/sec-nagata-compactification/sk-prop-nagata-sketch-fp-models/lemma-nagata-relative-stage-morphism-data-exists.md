+++
id = "lemma-nagata-relative-stage-morphism-data-exists"
kind = "lemma"
title = "Existence of finite-stage data for a finite-type morphism"
order = 381
uses = ["def-nagata-relative-stage-morphism-data", "lemma-nagata-directed-finite-upper-bound", "lemma-nagata-filtered-colimit-finite-data"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

If $S$ is qcqs and $X\to S$ is locally of finite type with $X$
quasi-compact and quasi-separated, then a finite-stage datum exists after enlarging both
indices. Its chart maps use only finitely many coefficients and relations,
and their base change to $S$ is the original morphism.

## Proof

Choose finite affine presentations of source and target charts. Their
finitely many coefficients, structural maps, and overlap identities occur
at one common stage by the finite-data lemma; enlarging both indices gives
the required compatible datum and immersion charts.
