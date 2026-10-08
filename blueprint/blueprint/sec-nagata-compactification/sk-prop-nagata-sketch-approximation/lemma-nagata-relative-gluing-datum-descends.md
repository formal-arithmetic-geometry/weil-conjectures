+++
id = "lemma-nagata-relative-gluing-datum-descends"
kind = "lemma"
title = "Property of the descended finite affine presentation"
order = 359
uses = ["def-nagata-relative-gluing-datum-descent", "lemma-nagata-affine-fp-descends", "lemma-nagata-morphism-descends", "lemma-nagata-qc-open-descends"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

Every chart, overlap open, and overlap map in the constructed raw datum
base changes to its named counterpart in $\mathsf R_X$.

## Proof

Apply the corresponding property lemma to each finite-presentation chart,
quasi-compact overlap, and overlap morphism. There are only finitely many
objects, and the common upper bound transports all of them to one stage
without changing their base changes.
