+++
id = "lemma-nagata-glue-noetherian-stage"
kind = "lemma"
title = "Properties of the finite-type stages"
order = 341
uses = ["def-nagata-noetherian-inverse-system", "lemma-nagata-affine-gluing-identities-eventually", "lemma-nagata-valid-refinements-directed"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

Every $S_\lambda$ is of finite type over $\mathbf Z$, and every transition
morphism $t_{\mu\lambda}$ is affine.

## Proof

The gluing axioms hold at each valid stage, so the schemes are defined.
Each one is covered by finitely many spectra of finitely generated
$\mathbf Z$-algebras, proving finite type. On the chosen charts each
transition is affine by construction; the indexing refinement makes those
charts cover every inverse image, proving global affineness.
